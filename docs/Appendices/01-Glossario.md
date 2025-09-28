# Appendice A — Glossario Tecnico

| Termine | Definizione | Riferimento | Stato |
|---------|-------------|-------------|-------|
| ATT (Active Transaction Table) | Dizionario `txId -> lastLSN` ricostruito nella fase di analisi ARIES. | `Database+GlobalWALRecovery.swift` | Implementato |
| DPT (Dirty Page Table) | Mappa `pageId -> recLSN` delle pagine sporche al momento del crash. | `analysisPhase` | Implementato |
| LSN (Log Sequence Number) | Numero sequenziale assegnato ai record WAL. | `FileWALManager` | Implementato |
| CLR (Compensation Log Record) | Record WAL generato durante UNDO per garantire idempotenza. | `WALCLRRecord` | Implementato |
| MVCC | Multi-Version Concurrency Control, permette letture non bloccanti mantenendo versioni. | `Transactions/MVCC.swift` | Implementato (parziale) |
| WAL | Write-Ahead Log: garantisce durabilità registrando modifiche prima dei dati. | Parte II, Cap. 5 | Implementato |
| Snapshot | Stato visibile a una transazione MVCC. | `MVCCSnapshot` | Implementato |
| Free Space Map | Struttura per scegliere pagine con spazio libero. | `FreeSpaceMap` | Implementato |
| Cost Estimator | Modulo che stima i costi per il planner fisico. | `CostEstimator` | Implementato |
| Group Commit | Batch di record WAL scritto atomicamente per ridurre i fsync. | `groupCommitSync` | Implementato |
| Checkpoint Catalog | Serializzazione di DPT/ATT e metadati durante checkpoint. | `CheckpointCatalog` | Implementato |
| Logical Plan | Piano di operatori algebrici derivato dal SQL. | `LogicalPlanner` | Implementato |
| Physical Plan | Piano con operatori concreti (scan, join) basato su costi stimati. | `PhysicalPlanner` | Implementato |
| Executor | Motore iterator-based che valuta il piano fisico. | `Executor` | Implementato |
| Buffer Frame | Slot del buffer pool contenente una pagina e stato associato. | `BufferFrame` | Implementato |
| Passo ARIES | Fase di Analisi/REDO/UNDO per il recovery. | Cap. 5 | Implementato |
| Catalog Snapshot | Stato JSON del catalogo (logico/fisico/stats). | `SystemCatalog` | Implementato |
| WAL Metrics | Misure di throughput e latenza del WAL. | `WALMetrics` | Implementato |
