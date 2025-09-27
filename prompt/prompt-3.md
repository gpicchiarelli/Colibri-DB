# ColibrìDB — Ottimizzazioni e Strutture Dati Consigliate (Swift 6, Apple Silicon)

> Documento tecnico sulle **migliori strutture dati**, scelte architetturali e ottimizzazioni pratiche per implementare ColibrìDB (RDBMS in Swift 6) con obiettivi di **milioni di connessioni logiche**, alta concorrenza, volumi elevati e massima efficienza su **hardware Apple**.

---

## 1. Principi guida
- **Protocol-first design**: tutte le strutture dati sono nascoste dietro protocolli (es. `IndexProtocol`, `TableStorageProtocol`), per poter **sostituire** implementazioni senza impatti a monte.
- **Località**: ottimizzare per cache CPU/L1/L2, favorendo scorrimenti sequenziali e accessi prevedibili.
- **Contesa ridotta**: limitare lock globali, preferire **sharding/partitioning** e lock a granolarità fine; introdurre **lock-free** dove sensato.
- **I/O consapevole**: batching, pagine fisse (4–8 KB), scritture append-only dove possibile (WAL, LSM), fsync ordinati.
- **Misurabilità**: metriche e tracing integrati (os_log/signpost) per guidare scelte e regressions.

---

## 2. Storage a record (row-oriented) — Heap file paginati
**Scelta MVP**: **Heap file** con **slot directory** su pagina (4/8 KB), adatto a carichi OLTP generici.
- **Struttura pagina**: header (id, pageLSN, free space), slot directory (array di offset), area dati variabile.
- **Vantaggi**: inserimenti veloci (append nella pagina o nuova pagina), supporto a record variabili (TEXT) con forwarding se necessario.
- **Ottimizzazioni**:
  - **Free space map** globale per trovare rapidamente pagine con spazio sufficiente.
  - **Slab/arena allocator** per metadati interni.
  - **Zone map** a livello di estensione/pagina per accelerare scansioni su colonne monotone.

**Alternative** (per workload specifici):
- **PAX/NSM ibrido**: riorganizzazione per colonna dentro la pagina per scansioni su poche colonne (compatibile con row store).
- **Colonnare** (in roadmap): migliore per analytics; richiede operatori vectorized e compressioni spinte.

---

## 3. Indici: scelte e trade-off

### 3.1 Hash Index (Equality)
**Uso**: ricerche `WHERE col = value`, alta selectivity o key lookup.
- Implementazione **persistente** a buckets + overflow, directory ridimensionabile (extendible hashing) o **linear hashing**.
- **Pro**: lookup O(1) atteso, throughput alto in write-heavy se ben dimensionato.
- **Contro**: pessimo per range scan / ORDER BY.
- **Ottimizzazioni**:
  - **Cache-aware** bucket sizing, ridurre collisioni.
  - **Bloom filter** per evitare accessi a bucket vuoti su dischi.
  - **Concurrency**: lock a bucket o striping locks; crescita graduale (rehash incrementale).

### 3.2 B+Tree (Range + Order)
**Uso**: range scan, ORDER BY, BETWEEN; indice secondario universale.
- **Pro**: eccellente per range; stabile in presenza di grandi dataset; amichevole al buffer pool.
- **Contro**: gestione split/merge; più costoso del hash su equality pura.
- **Ottimizzazioni**:
  - **Nodo ampio** (pagine intere) per sfruttare I/O sequenziale e minori livelli.
  - **Sibling/next pointers** per scansioni ordinarie efficienti.
  - **Fence keys** per verifiche consistenza.
  - **Latch coupling** (o B-link trees) per concorrenza elevata.
  - **Bulk build** per creazione indice a partire da dati ordinati.

### 3.3 Alternative moderne (da valutare / pluggabili)
- **Bw-Tree** (lock-free B-Tree con delta records): ottimo in concorrenza alta, ma complesso; richiede mappa pagine logiche → fisiche.
- **ART (Adaptive Radix Tree)**: radici radici adattive per chiavi binarie; lookup velocissimo, cache-friendly; eccellente per string/UUID.
- **SkipList** persistenti: semplici e buone per concorrenza; costi maggiori in spazio.
- **Fractal Tree** (es. TokuDB): ottimo per write-heavy, batching degli update lungo il path.
- **LSM-Tree** (vedi §4): per workload write-heavy massivi, con compaction programmata.

**Raccomandazione**: MVP con **Hash + B+Tree**. Protocolli aperti per **ART** in futuro (specialmente per chiavi testo) e **Bw-Tree** per esperimenti su lock-free.

---

## 4. Motore write-heavy: LSM-Tree ibrido (opzionale/esteso)
Per ingest elevatissimi, valutare uno **storage engine LSM** (Log-Structured Merge):
- **Memtable** (SkipList/hash in RAM) + **SSTables** append-only su disco, **compaction** in background.
- **Pro**: scritture sequenziali, ottime su NVMe; throughput ingest elevato.
- **Contro**: latenza letture peggiore (necessari **Bloom filters**, cache calda), gestione compaction.
- **Ibrido**: mantenere row-store per OLTP e usare LSM per tabelle specifiche (via `TableStorageProtocol`).

---

## 5. MVCC e versioning dei record
**Obiettivo**: letture non bloccanti e snapshot consistenti.
- **Schema record**: `createTID`, `deleteTID` (o `validFrom/validTo`).  
- **Visibilità**: funzione `visible(record, snapshot)` senza lock in lettura.
- **Garbage collection**: vacuum versioni obsolete post-checkpoint/commit globale.
- **Ottimizzazioni**:
  - **Append-only** per nuove versioni → scritture sequenziali.
  - **Version chain** corta: favorire consolidamento su UPDATE multipli.

---

## 6. Lock manager & Deadlock detection
- **Strutture dati**:
  - **Hash map** (key → lock state) shardata per ridurre contesa.
  - **Wait-for graph** per detection (grafo diretto in memoria + BFS/DFS periodico).
- **Lock modes**: S, X (+ upgrade). Escalation a tabella per storm di lock granulari.
- **Ottimizzazioni**:
  - **Partitioned locks** per hot tables/indices.
  - **TryLock + backoff con jitter** per evitare thundering herd.
  - **Timeout** configurabili, metrics sui wait.

---

## 7. Buffer Pool (politiche e strutture)
- **Tabella pagine**: hash map → frame; **clock/clock-pro** o **2Q** come politica di eviction (più semplice e performante di LRU pura).
- **Hot/cold segmentation** (2Q/ARC) per pattern misti (scan + hotspot).
- **Pinned pages** per pagine radice indici e header.
- **Write-back** batch con ordini di pagina per massimizzare I/O sequenziale.

---

## 8. Compressione e codifiche
- **Pagina**: compressione leggera **LZ4** per paging più denso (I/O bound).  
- **Colonnare** (in roadmap): **RLE**, **Dictionary encoding**, **Delta encoding**, **Bitpacking**.  
- **WAL**: compressione blocchi opzionale (soprattutto su NVMe veloci la CPU è spesso il collo di bottiglia — misurare!).

---

## 9. Filtri e metadati acceleratori
- **Bloom filters**: per LSM/SSTables, per predicati `=`, riducendo falsi accessi disco.
- **Zone maps**: min/max per pagina/extent su colonne ordinate/monotone → salto rapido in scansioni.
- **Covering index**: includere colonne extra nel B+Tree per soddisfare query senza accesso alla tabella (index‑only).

---

## 10. Esecuzione query: Volcano vs Vectorized
- **Volcano (iterator-one-tuple)**: semplice, composabile; ottimo per OLTP.
- **Vectorized (batch-of-tuples)**: blocchi da N tuple per ridurre overhead di chiamata e favorire SIMD (Accelerate).  
**Strategia**: mantenere Volcano per OLTP; introdurre operatori **vectorized** per scansioni/aggregazioni su dataset grandi (modalità analytics).

---

## 11. Allocatori di memoria
- **Arena/Slab** per oggetti a vita legata alla query/transazione (alloc/dealloc in blocco).  
- **Object pools** per riciclare strutture temporanee (iterators, cursori).  
- Evitare allocazioni frequenti in hot path (usare `withUnsafe*` con cura e misurare).

---

## 12. Ottimizzazioni Apple Silicon / macOS
- **CRC32 hardware** (ARMv8) per pagine e WAL (binding C).  
- **APFS clone** per `\backup` (copy‑on‑write istantaneo).  
- **F_FULLFSYNC** quando servono garanzie massime (documentare l’impatto).  
- **F_NOCACHE / F_RDAHEAD** su file di dati in scenari specifici.  
- **Swift Concurrency** (actors) per isolation dati; evitare false sharing (padding struct).  
- **Instruments** per profilare: Time Profiler, System Trace, Allocations, I/O.  
- **Accelerate/vDSP** per aggregazioni vectorized; **Compression** per LZ4/ZSTD.

---

## 13. Sicurezza by design
- **Cifratura a riposo**: AES‑GCM via CryptoKit; chiavi in Keychain/Secure Enclave se possibile.  
- **Cifratura in transito**: TLS su modulo server.  
- **Checksum e autenticazione pagina**: evitare data corruption silenziosa.  
- **Audit log** append-only; protezione file di log.  
- **Least privilege**: permessi minimi su data dir; separazione ruoli in CLI.

---

## 14. Import/Export (CSV/JSON/BSON) — performance tips
- **CSV**: parser streaming (line‑by‑line), inferenza tipi opzionale, batch insert (N per commit).  
- **JSON**: streaming decoder, evitare DOM completo; mapping tipi configurabile.  
- **BSON**: parsing binario, batch write.  
- **Parallel ingest**: più worker con partizionamento per chiave per minimizzare lock contention sugli indici.

---

## 15. Scelte consigliate per scenari tipici

| Scenario | Tabella | Indice primario | Indici secondari | Note |
|---|---|---|---|---|
| OLTP chiavi uniche | Heap (row) | B+Tree su PK | Hash/B+Tree | PK per range/ordine; Hash per lookup frequenti |
| Log/eventi write-heavy | LSM ibrido | Hash su id | Bloom + zone maps | Compaction in background |
| Cataloghi testuali | Heap/PAX | ART su testo | B+Tree | ART accelera prefix/lookup stringhe |
| Analytics letture pesanti | Colonnare (roadmap) | — | B+Tree per partition pruning | Operator vectorized + compressione |
| Time-series | Heap segmentato / LSM | B+Tree su (ts, id) | Zone maps per ts | Partizionamento per finestra temporale |

---

## 16. Pseudocodice interfacce (Swift-Style)

```swift
protocol IndexProtocol {
    associatedtype Key: Comparable & Hashable
    associatedtype Ref  // RID: (pageId, slotId)
    mutating func insert(_ k: Key, _ r: Ref) throws
    func searchEquals(_ k: Key) throws -> [Ref]
    func range(_ lo: Key?, _ hi: Key?) throws -> [Ref]  // opzionale per Hash
    mutating func remove(_ k: Key, _ r: Ref) throws
}
```

```swift
protocol TableStorageProtocol {
    mutating func insert(_ row: Row) throws -> RID
    func scan() throws -> AnySequence<(RID, Row)>
    func read(_ rid: RID) throws -> Row
    mutating func update(_ rid: RID, _ newRow: Row) throws
    mutating func remove(_ rid: RID) throws
}
```

```swift
struct BloomFilter {
    private var bits: [UInt64]
    private let seeds: [UInt64]
    mutating func add(_ h: UInt64) { /* set k bit positions */ }
    func mightContain(_ h: UInt64) -> Bool { /* check */ }
}
```

---

## 17. Tuning iniziale (valori di default suggeriti)
- **pageSize**: 8192 bytes (8 KB) su NVMe moderni.  
- **bufferPoolSize**: 1–4 GB (sviluppo) → aumentare in produzione.  
- **checkpointInterval**: 60 s (misurare).  
- **hashLoadFactor**: 0.7.  
- **bptreeNodeFill**: ~70–80%.  
- **walCompression**: off (abilitare se I/O bound).  
- **actorConcurrencyLevel**: #Performance cores.

---

## 18. Metriche chiave da esporre (CLI `coldb` / metrics)
- **TPS/QPS**, p95/p99 latenza query.  
- **Buffer hits/miss**, evictions, dirty flush/sec.  
- **WAL LSN**, write rate, backlog.  
- **Lock waits**, deadlocks, tempo medio lock hold.  
- **Index stats**: altezza B+Tree, load factor hash, bloom fp‑rate.  
- **GC MVCC**: versioni per pagina, vacuum throughput.

---

## 19. Roadmap tecnica strutture dati
- **B+Tree** concorrente (B-link) → **ART** per chiavi stringa.  
- **Vectorized engine** per scansioni e aggregazioni; compressione colonnare.  
- **LSM** ibrido con compaction consapevole di Apple NVMe.  
- **Bw-Tree** sperimentale per lock-free scans/updates ad alta contesa.  
- **GPU offload** (da valutare in lontana roadmap) per aggregazioni massicce.

---

## 20. Conclusioni
Le scelte proposte massimizzano **robustezza, prestazioni e flessibilità** su Apple Silicon. L’adozione di protocolli per indici e storage consente di **plug‑gare** strutture alternative (anche inventate) senza toccare Planner/Executor. Misurazioni continue guideranno l’evoluzione (Volcano per OLTP, vectorized per analytics), mantenendo **sicurezza, integrità e durabilità** come requisiti non negoziabili.
