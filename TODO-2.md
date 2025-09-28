# ColibrDB — Piano di Lavoro verso RDBMS Completo profilato.

---
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

- [ ] Tabelle per oggetti logici (tabelle, indici, viste, sequenze).  
- [ ] Tabelle per oggetti fisici (file, pagine, segmenti).  
- [ ] Tabelle ruoli/permessi (utenti, gruppi, privilegi).  
- [ ] Tabelle statistiche (cardinalità, istogrammi, distribuzioni).  
- [ ] Tabelle configurazioni (parametri runtime, politiche eviction, tipo di indice usato).  
- [ ] Persistenza delle scelte di struttura dati (B+Tree vs ART vs LSM) a livello catalogo.  


## Core Storage & Durabilità
🎯 Obiettivo: garantire persistenza crash-safe, gestione buffer pool efficiente, telemetria base.

- [x] Pagine dati su disco (heap) con free space map persistente (FSM sidecar, first-fit) ✅ [MVP]
- [x] Buffer pool con eviction policy (Clock, LRU-2 approx) e flusher in background (timer + maxDirty) ✅ [MVP]
- [x] WAL v1 (CRC32, LSN, tipi base) con checkpoint ✅ [MVP]
- [x] Recovery REDO idempotente (match riga) ✅ [MVP]
- [x] Transaction log (BEGIN/COMMIT/ROLLBACK + typed records) ✅ [MVP]
- [ ] Recovery ARIES-like completo (Analysis, REDO, UNDO con CLRs, PageLSN rigoroso) [ALPHA]
- [ ] Namespace separati (tabelle/indici) con limiti dedicati (configurabile) [MVP]
- [ ] Telemetria buffer pool (/stats, \bp) [MVP]
- [ ] Compattazione heap e FSM update [MVP]

---

## Indici
🎯 Obiettivo: fornire indici scalabili e pluggabili.

- [x] B+Tree persistente (insert/split, range, composite) ✅ [MVP]
- [x] Bilanciamento foglie/interne, collasso root ✅ [MVP]
- [x] Bulk build bottom-up + WAL indici v1 ✅ [MVP]
- [x] Adaptive Radix Tree (ART) con traversal DFS ✅ [MVP]
- [ ] Prefix compression + varint optimization [ALPHA]
- [ ] Compattazione online indici (threshold + scheduling) [ALPHA]
- [ ] Statistiche cardinalità e frammentazione (input ottimizzatore) [BETA]
- [ ] Indici alternativi: SkipList, Fractal Tree, LSM [BETA]

---

## Concurrency & Transazioni
🎯 Obiettivo: isolamento transazionale, MVCC, deadlock-safe.

- [ ] MVCC con visibility e vacuum [ALPHA]
- [ ] Lock manager con deadlock detection [ALPHA]
- [ ] Isolamento configurabile (Read Committed → Serializable) [ALPHA]
- [ ] Partial rollbacks [BETA]
- [ ] Write intents / logical locks per DDL [BETA]
- [ ] Two-phase commit (2PC) per cluster [FUTURE]

---

## Planner & Executor
🎯 Obiettivo: query engine con Volcano model e ottimizzatore cost-based.

- [ ] Operatori Volcano: scan, filter, project, sort, join [ALPHA]
- [ ] ORDER BY / index scan accelerati [ALPHA]
- [ ] Predicate pushdown con indici compositi [ALPHA]
- [ ] Istogrammi per stime cardinalità [BETA]
- [ ] Ottimizzatore cost-based [BETA]
- [ ] Join multipli (hash join, merge join) [BETA]
- [ ] Query parallele (multi-thread/actor) [BETA]
- [ ] Materialized views + caching [FUTURE]

---

## SQL & Tipi di dati
🎯 Obiettivo: parser SQL con DDL/DML/DCL, tipi base e funzioni aggregate.

- [ ] Parser SQL completo (ANTLR/handwritten) [ALPHA]
- [ ] CREATE/ALTER/DROP TABLE [ALPHA]
- [ ] Constraint: PK, FK, Unique, Check [ALPHA]
- [ ] Trigger e Stored Procedures base [BETA]
- [ ] Funzioni aggregate (COUNT, SUM, AVG, MIN, MAX) [ALPHA]
- [ ] Built-in (date, stringhe, numeri) [ALPHA]
- [ ] Tipi scalari: INT, BIGINT, TEXT, VARCHAR, BOOL, DECIMAL [MVP]
- [ ] Tipi complessi: BYTEA/BLOB, JSON, ENUM [ALPHA]

---

## Catalogo & Metadata
🎯 Obiettivo: catalogo persistente e statistiche ottimizzatore.

- [ ] Catalogo tabelle, indici, attributi [ALPHA]
- [ ] Statistiche cardinalità/istogrammi [BETA]
- [ ] Versioning schema con ALTER [BETA]
- [ ] Metadata utenti/ruoli/permessi [BETA]

---

## CLI & Server
🎯 Obiettivo: CLI avanzata + server remoto compatibile Postgres/MySQL.

- [x] CLI indici (search/range/validate/rebuild) ✅ [MVP]
- [x] Delete predicate equality ✅ [MVP]
- [x] Import/Export CSV (header row) ✅ [MVP]
- [ ] Import/Export JSON/BSON streaming [ALPHA]
- [ ] Server remoto con SwiftNIO (TLS, auth, audit) [ALPHA]
- [ ] Protocollo wire compatibile Postgres/MySQL [BETA]
- [ ] Driver nativo Swift (async/await, Codable) [BETA]
- [ ] REST/gRPC API [BETA]
- [ ] Connection pooling lato server [BETA]

---

## Sicurezza
🎯 Obiettivo: protezione dati e compliance.

- [x] BSD-3-Clause license header ✅ [MVP]
- [ ] AES-GCM cifratura file dati/indici/WAL [ALPHA]
- [ ] Key management (Keychain, Secure Enclave) [ALPHA]
- [ ] Scrubbing spazio libero su delete [BETA]
- [ ] Autenticazione pluggabile (password, OAuth, cert) [BETA]
- [ ] Ruoli, GRANT/REVOKE [BETA]
- [ ] Row-level security (RLS) [FUTURE]
- [ ] Mascheramento dati sensibili (GDPR/PII) [FUTURE]
- [ ] Audit log completo [BETA]

---

## Apple Silicon / APFS
🎯 Obiettivo: sfruttare pienamente HW Apple + APFS.

- [ ] F_FULLFSYNC, APFS snapshot/cloni/sparse, hint I/O (F_RDADVISE, preadv2) [ALPHA]
- [ ] SIMD (NEON), Accelerate/vDSP, MPS/BNNS, Core ML/Neural Engine [BETA]
- [ ] Secure Enclave + CryptoKit per cifratura [ALPHA]
- [ ] Compressione HW (LZFSE/Zlib), CRC32 ARMv8 [ALPHA]
- [ ] Unified Memory profiling + energy tuning [BETA]
- [ ] Rosetta2 compatibilità + Universal Binary [MVP]
- [ ] DTrace/Instruments, Signpost, Unified Logging [BETA]

---

## Amministrazione & Operazioni
🎯 Obiettivo: garantire manutenzione, replica e osservabilità.

- [ ] Backup incrementali + PITR dal WAL [ALPHA]
- [ ] Replica WAL streaming [BETA]
- [ ] Sharding/partizionamento (hash/range/list) [BETA]
- [x] Vacuum/autovacuum programmato ✅ [MVP]
- [ ] Dashboard CLI/web per metriche runtime [BETA]

---

## Test & QA
🎯 Obiettivo: garantire affidabilità con test e fault-injection.

- [ ] Unit test B+Tree/ART (split, merge, prune) [MVP]
- [ ] Stress test WAL replay + fuzzing [ALPHA]
- [ ] Fault-injection demo (CLI) [ALPHA]
- [ ] Benchmark micro/macro [ALPHA]
- [ ] Endurance test con crash simulated [BETA]
- [ ] Test SQL parser/linguaggio [ALPHA]
- [ ] Test sicurezza + cifratura [BETA]
- [ ] Test networking/protocollo wire [BETA]

---

## Estensioni (Future Roadmap)
🎯 Obiettivo: features avanzate oltre OLTP.

- [ ] Supporto grafi (Cypher/Gremlin) [FUTURE]
- [ ] Funzioni analitiche (window functions) [FUTURE]
- [ ] Storage colonnare (ibrido OLAP/OLTP) [FUTURE]
- [ ] Engine LSM opzionale [FUTURE]