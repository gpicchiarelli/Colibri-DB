# ColibrìDB — Piano di Lavoro verso RDBMS Completo

## Principi guida
- Ogni componente deve essere progettato per la **massima velocità e throughput**, riducendo al minimo la latenza.  
- Prediligere algoritmi **branchless**, ottimizzati per cache locality e SIMD (NEON).  
- Ottimizzare I/O per **scritture sequenziali** e ridurre il random I/O.  
- Usare **lock-free structures** o ridurre al minimo la contesa nei percorsi critici.  
- La telemetria e gli strumenti di debug devono introdurre overhead **trascurabile**.  
- Ogni milestone deve essere validata tramite **benchmark micro/macro** e test di regressione sulle performance.  

---

## Catalogo di Sistema
🎯 Obiettivo: tutte le informazioni su oggetti, metadati e configurazioni devono confluire nel **catalogo** (system tables), unico punto di verità.

- [x] Tabelle per oggetti logici (tabelle, indici, viste, sequenze).  
- [x] Tabelle per oggetti fisici (file, pagine, segmenti).  
- [x] Tabelle ruoli/permessi (utenti, gruppi, privilegi).  
- [x] Tabelle statistiche (cardinalità, istogrammi, distribuzioni).  
- [x] Tabelle configurazioni (parametri runtime, politiche eviction, tipo di indice usato).  
- [x] Persistenza delle scelte di struttura dati (B+Tree vs ART vs LSM) a livello catalogo.  

## Core Storage & Durabilità
- [x] Pagine dati su disco (heap) con free space map persistente (v1: sidecar .fsm, first-fit)
- [x] LRU buffer pool: pin/unpin, dirty tracking, flush differito (supporto)
- [x] Politiche eviction avanzate (Clock, LRU-2 approx) in buffer pool
- [x] Flusher in background e soglie di write-back (timer + maxDirty)
- [x] WAL completo (DB): record strutturati, LSN, checksum, checkpoint
- [x] WAL DB v1: record strutturati (CRC32, LSN, tipi), checkpoint
- [x] Recovery REDO (MVP) con idempotence basata su match riga
- [x] UNDO/transaction log (begin/commit, abort) [MVP già presente]
- [x] Test fault-injection (framework + CLI: \\fault set/clear)
- [x] Namespace separati (tabelle/indici) con limiti dedicati
- [x] Namespace separati (tabelle/indici) con limiti dedicati (config)
- [x] Telemetria dettagliata (hit/miss, evict, pinned, dirty) esposta via CLI (\\bp, \\stats)
- [x] Compattazione pagina heap e aggiornamento FSM

## Indici
- [x] B+Tree persistente (insert/split, range, composite)
- [x] WAL indici v1 (insert/delete/checkpoint, CRC32, LSN)
- [x] Bilanciamento foglie e interni (borrow/merge), collasso root
- [x] Bulk build bottom-up e checkpoint con pageLSN (v1 parziale)
- [x] ART: range traversal corretto (ordine byte), ricostruzione chiave in DFS
- [x] PageLSN su tutte le pagine (foglie incluse), validation
- [x] Delete multi-RID e compattazione fisica (B+Tree persistente)
- [x] Prefix compression chiavi e riduzione overhead varint
- [x] Deframmentazione/compattazione online (soglie + scheduling)
- [x] Statistiche frammentazione e cardinalità per ottimizzatore
- [x] Alternative indici pluggabili (SkipList, Fractal Tree, LSM engine)

## Concurrency & Transazioni
- [x] MVCC con visibility e vacuum
- [x] Lock manager e deadlock detection
- [x] Isolamento configurabile (Read Committed → Serializable)
- [x] Clock-SI/Serializable snapshot (design)
- [x] Garbage collection RIDs orfane su drop index
- [x] Write intents / logical locks per DDL
- [x] Partial rollbacks
- [x] Two-phase commit (2PC) per cluster/distribuito
- [x] Transaction manager (MVP): BEGIN/COMMIT/ROLLBACK + WAL typed records
- [x] Recovery ARIES-like completo (REDO/UNDO con CLRs, LSN/pageLSN rigidi)

## Planner/Executor
- [ ] Operatori Volcano (scan, filter, project, sort, join)
- [ ] ORDER BY/INDEX scan accelerati
- [ ] Predicate pushdown vs indici compositi (leading/prefix)
- [ ] Stime cardinalità basate su istogrammi
- [ ] Ottimizzatore cost-based completo
- [ ] Join multipli (hash join, merge join)
- [ ] Query parallele (multi-thread, actor)
- [ ] Materialized views e caching query

## Linguaggio SQL & Tipi di dati
- [ ] Parser SQL completo (DDL, DML, DCL)
- [ ] CREATE TABLE / ALTER / DROP
- [ ] Constraint: PK, Unique, Not Null, FK, Check
- [ ] Trigger & Stored Procedures
- [ ] Funzioni aggregate di base (COUNT, SUM, AVG, MIN, MAX)
- [ ] Funzioni built-in per tipi base (date/time, stringhe, numeri)
- [ ] Tipi: INT, BIGINT, TEXT, VARCHAR, BOOL, DATE/TIME, DECIMAL
- [ ] Tipi binari (BLOB, BYTEA)
- [ ] Tipi JSON con indexing
- [ ] ENUM

## Metadata & Catalogo
- [ ] Catalogo di sistema persistente (tabelle, indici, attributi)
- [ ] Statistiche per ottimizzatore (cardinalità, istogrammi)
- [ ] Versioning schema con ALTER TABLE
- [ ] Informazioni sugli utenti/ruoli e permessi

## CLI & Server
- [x] CLI indici (search/range/validate/rebuild/bulk-build)
- [x] Delete di base (predicate equality)
- [x] Import/Export CSV (CLI, header row; MVP)
- [ ] Import/Export streaming (JSON/BSON)
- [ ] Server remoto (SwiftNIO) + autenticazione + audit log
- [ ] Protocollo wire compatibile (Postgres/MySQL)
- [ ] Driver nativo Swift (async/await + Codable)
- [ ] API REST/gRPC opzionali
- [ ] Connection pooling lato server
- [x] Esportazione metriche Prometheus (CLI \stats prometheus)
- [ ] Script helper per benchmark e carichi

## Sicurezza
- [x] License BSD-3-Clause header
- [x] CRC32 per WAL indici
- [ ] Cifratura a riposo (AES-GCM) per file dati/indici/WAL
- [ ] Key management (Keychain/Secure Enclave)
- [ ] Scrubbing spazio libero (page wipe) su delete
- [ ] Autenticazione pluggabile (password, OAuth, certificati)
- [ ] Autorizzazione basata su ruoli (GRANT/REVOKE)
- [ ] Row-level security (RLS)
- [ ] Mascheramento dati sensibili (GDPR/PII)
- [ ] Audit log completo

## Apple Silicon / APFS
- [ ] F_FULLFSYNC, flag file e tuning I/O
- [ ] APFS snapshot per \backup
- [ ] QoS e I/O priority per thread di flush
- [x] CRC32 hardware ARMv8
- [ ] Accelerate/vDSP per operatori vectorized
- [ ] Instruments/os_log per tracing
- [ ] NEON intrinsics (ARMv8 SIMD) per comparazioni, hash e scansioni
- [ ] CryptoKit / Secure Enclave per cifratura e autenticazione hardware
- [x] Compressione hardware (LZFSE/Zlib) per pagine e WAL
- [ ] Memory Tagging Extension (MTE) e Address Sanitizer per debug memoria
- [ ] Profiling Unified Memory per buffer pool (CPU/GPU condivisa)
- [ ] APFS Clones per snapshot rapidi a livello tabella/indice
- [ ] APFS Sparse Files per allocazioni heap/indici efficienti
- [ ] Integrazione con cifratura APFS/FileVault
- [ ] Grand Central Dispatch QoS classes per WAL/flush
- [x] Signpost API (os_signpost) per tracing eventi in Instruments
- [ ] Compatibilità Rosetta 2 per esecuzione cross-arch
- [ ] Metal Performance Shaders (MPS) / Accelerate per calcoli analitici futuri
- [ ] Page Fusion VM macOS per deduplicazione pagine (sperimentale)
- [ ] Unified Logging (OSLogStore) per analisi log persistenti e I/O tracing
- [ ] EndpointSecurity / Transparency logs per auditing e compliance
- [ ] Core ML / Neural Engine per ottimizzazioni future (es. query optimizer ML-based)
- [ ] Network.framework QoS e TLS nativo per il server remoto
- [x] I/O hints API (fcntl F_RDADVISE) per pattern di lettura sequenziali/prefetch
- [x] POSIX_FADV / preadv2 per hint di accesso random/sequenziale su APFS
- [ ] DTrace / Instruments avanzato per lock contention e syscalls
- [ ] Ottimizzazioni energia (low power mode) su laptop Apple Silicon
- [ ] Universal Binary ARM64 + x86_64 per compatibilità cross-Mac
- [ ] FS snapshots differenziali APFS per PITR incrementale

## Amministrazione & Operazioni
- [ ] Backup incrementali oltre ad APFS snapshot
- [ ] Point-in-time recovery (PITR) dal WAL
- [ ] Replica log-based (streaming WAL)
- [ ] Sharding/partizionamento (hash/range/list)
- [x] Vacuum & autovacuum programmato (timer, metriche CLI)
- [ ] Dashboard CLI/web per metriche runtime

## Test & QA
- [x] Test integrazione MVCC (isolamento + vacuum)
- [x] Test integrazione 2PC coordinator
- [ ] Test unitari indici (split/merge/borrow, validate-deep)
- [ ] Test unitari ART (equality/range, compressione path, prune)
- [ ] Stress/WAL replay e fuzzing
- [ ] Preparare uno script di fault-injection (CLI) che dimostri il recovery con un caso reale
- [ ] Benchmark micro/macro
- [ ] Test endurance con interruzioni e crash simulated
- [ ] Test linguaggio SQL e parser
- [ ] Test sicurezza e cifratura
- [ ] Test networking e protocollo wire

## Roadmap Estensioni
- [ ] Supporto a grafi (Cypher/Gremlin-like)
- [ ] Funzioni analitiche (window functions)
- [ ] Storage colonnare (ibrido OLAP/OLTP)
- [ ] Engine LSM opzionale
