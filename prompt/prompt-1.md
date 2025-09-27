# PROMPT — ColibrìDB: RDBMS Swift 6 con storage su disco, **milioni di connessioni simultanee**, ottimizzato per Apple Silicon, CLI `coldb`, e strutture dati pluggabili

## Visione
Costruire **ColibrìDB**, un RDBMS scritto in Swift 6, modulare e robusto (**ACID**), con persistenza su disco, capace di scalare fino a **milioni di connessioni simultanee**, massimizzando le performance su **hardware Apple** (Apple Silicon, APFS, NVMe) e offrendo una **CLI completa** (`coldb`) per interazione e manutenzione.  
Il sistema deve essere sicuro, affidabile e conforme agli standard attesi per la gestione di **dati critici o sensibili**.

Architettura a strati: **StorageEngine** (file‑backed) · **Planner** · **Executor** · **Transaction/Concurrency** · **CLI** · (**Server opzionale** per accessi remoti).  
Stile: Swift 6 puro, **protocol‑first**, `struct` per dati, `final class` per oggetti con identità, errori tipizzati, doc comments completi.

---

## Requisiti funzionali principali
- **Storage su disco**: heap file paginati, catalogo persistente, indici persistenti.  
- **WAL & Recovery**: Write‑Ahead Logging crash‑safe, checkpoint, redo/undo.  
- **Buffer Pool**: cache di pagine con politiche configurabili.  
- **Transazioni e concorrenza**: Lock manager, MVCC, deadlock detection.  
- **Planner & Executor**: scelta piani fisici, esecuzione iteratore Volcano.  
- **CLI `coldb`**: interfaccia interattiva e batch, comandi amministrativi, manutenzione, metriche.  
- **Server**: protocollo multiplexato per accessi remoti (SwiftNIO/kqueue).

---

## Concorrenza estrema
- Supporto ad almeno **1.000.000 di sessioni logiche simultanee** con throughput stabile.  
- Multiplexing e session virtualization su poche connessioni fisiche.  
- Runtime event‑driven con Swift Concurrency e I/O non bloccante.  
- Backpressure oltre `maxConnectionsLogical`, con messaggi chiari al client.

---

## Paradigmi multipli e strutture dati pluggabili
- Il sistema deve supportare **molteplici paradigmi di dati**, oltre al relazionale:  
  - **Relazionale** (SQL classico, tabelle e indici).  
  - **Grafi** (da valutare in seguito, con possibilità di query stile Cypher/Gremlin).  
  - **Documenti** (JSON/semistrutturati, roadmap).  
- Gli **indici** devono essere pluggabili tramite protocolli (`IndexProtocol`), permettendo overloading:  
  - Default: HashIndex e B+Tree.  
  - Estensioni possibili: SkipList, Fractal Tree, strutture inventate dall’utente.  
  - Comando: `CREATE INDEX ... USING <IndexType>`.  
- Le tabelle stesse devono poter adottare diversi **TableStorageProtocol** (heap, colonnare, grafo, ecc.).

---

## Sicurezza dei dati
ColibrìDB deve essere progettato per la gestione di **dati sensibili o critici**:  
- **Integrità**: checksum su pagine e WAL; verifiche consistenza all’avvio.  
- **Durabilità forte**: uso corretto di `fsync`/`F_FULLFSYNC` su APFS/NVMe per garantire atomicità anche in caso di crash.  
- **Crittografia**: supporto alla cifratura trasparente dei file (API CryptoKit/CCCrypt), gestione sicura delle chiavi.  
- **Autenticazione e autorizzazione**: utenti, ruoli, privilegi su tabelle/indici.  
- **Audit log**: registrazione accessi e comandi amministrativi.  
- **Conformità**: linee guida per protezione dati critici, GDPR e normative similari.  
- **Backup sicuri**: snapshot APFS clone con possibilità di cifratura.  
- **Isolamento transazioni**: livelli configurabili fino a Serializable per garantire coerenza.

---

## Ottimizzazioni Apple Silicon e APFS
- **CPU**: uso consapevole di Performance/Efficiency cores; scheduling attori su P‑cores per query, E‑cores per manutenzione/I/O.  
- **APFS**: sfruttare copy‑on‑write e clone file per backup (`coldb \\backup` istantanei).  
- **NVMe**: ottimizzare I/O sequenziale per checkpoint e vacuum; prefetch dati con hint kernel.  
- **File system flags**: `F_NOCACHE`, `F_RDAHEAD`, `F_FULLFSYNC` per controllare cache e durabilità.  
- **Checksum hw**: intrinsics ARMv8 CRC32 per verifiche rapide.  
- **Accelerate/vDSP**: per operazioni vectorizzate (scan, aggregazioni).  
- **CryptoKit**: per cifratura ed hash sicuri.  
- **os_log/signpost + Instruments**: tracing e profiling.  

---

## Configurazione
- `maxConnectionsLogical` (default 1M), `maxConnectionsPhysical` (default 8–16).  
- `bufferPoolSize`, `pageSize`, `walEnabled`, `checksumEnabled`.  
- `cliEnabled`, `metricsEnabled`, `serverEnabled`.  
- `indexImplementation = <Hash|BTree|Custom>` configurabile.  
- Config da file `colibridb.conf` + variabili ambiente + flag `coldb` CLI.

---

## Glossario
- **ACID** – Atomicità, Consistenza, Isolamento, Durabilità.  
- **MVCC** – Multi‑Version Concurrency Control: versioni record per letture concorrenti senza lock.  
- **WAL** – Write‑Ahead Logging: log su disco prima di scrivere i dati, per garantire durabilità.  
- **LSN** – Log Sequence Number: numero progressivo che identifica record nel WAL.  
- **Checkpoint** – Salvataggio di stato consistente per ridurre tempi di recovery.  
- **Actor (Swift)** – Meccanismo di isolamento concorrente in Swift Concurrency.  
- **Multiplexing** – Gestione di molte connessioni logiche sopra poche connessioni fisiche.  

---

## Roadmap a lungo termine
1. **Indici B+Tree** – per query range e ORDER BY.  
2. **Query parallele** – esecuzione distribuita su più core/attori.  
3. **Replica** – streaming WAL, replica asincrona per alta disponibilità.  
4. **Sharding** – partizionamento dati su più nodi.  
5. **Ottimizzatore cost‑based** – join order e stima costi basata su statistiche.  
6. **Supporto JSON/Document** – colonne JSON con indicizzazione nativa.  
7. **Funzioni analitiche** – window functions e aggregazioni avanzate.  
8. **Driver Swift** – integrazione con Codable, async/await.  
9. **Storage engine pluggable** – heap, colonnare, grafo, remoto.  
10. **High Availability** – consenso distribuito (Raft/Paxos) e failover automatico.  

---



---

## Import/Export dati (CSV, JSON, BSON)
ColibrìDB deve supportare in tutti i casi funzionalità di **import/export** per interoperabilità e migrazione:
- **CSV**: importazione tabelle da file delimitati, gestione header, encoding UTF‑8, escaping standard. Export tabelle o query in CSV.  
- **JSON**: import/export di record come oggetti JSON, mapping con tipi SQL. Supporto a nested JSON opzionale.  
- **BSON**: export/import in formato binario JSON (BSON), utile per interoperabilità con sistemi documentali.  
- Comandi CLI `coldb`:  
  - `\import <file.csv|json|bson> INTO <table>`  
  - `\export <table|query> TO <file.csv|json|bson>`  
- API Swift/driver: metodi `import(from:)`, `export(to:)` coerenti.  
- Devono essere rispettate le policy di sicurezza (cifratura, permessi) anche per i file di import/export.


## Criteri di accettazione
- Avvio DB con CLI `coldb` operativa.  
- Gestione di **≥ 1M connessioni logiche** con ammissione controllata.  
- Recovery WAL crash‑safe, nessuna corruzione.  
- Backup APFS clone sicuri e cifrati.  
- Indici pluggabili funzionanti (`CREATE INDEX ... USING ...`).  
- Dati sensibili trattati secondo best practice di sicurezza.  
- Metriche e log chiari; test unitari, integrazione e stress tutti verdi.  

---

### Nome progetto
**ColibrìDB** 🪶  
Veloce, leggero, resistente, sicuro.  
La sua CLI è **`coldb`**, semplice da ricordare e digitare.
