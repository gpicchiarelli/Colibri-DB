# Appendice A — Glossario Tecnico

| Termine | Definizione | Riferimento | Stato |
|---------|-------------|-------------|-------|
| ATT (Active Transaction Table) | Tabella delle transazioni attive usata in ARIES (mappa `txId -> lastLSN`). | `Database+GlobalWALRecovery.swift`, `WALCheckpointRecord`. | Implementato |
| DPT (Dirty Page Table) | Mappa delle pagine sporche con `recLSN`. | `analysisPhase` | Implementato |
| LSN (Log Sequence Number) | Numero sequenziale globale del WAL. | `FileWALManager`, `WALRecord`. | Implementato |
| CLR (Compensation Log Record) | Record WAL generato durante undo. | `WALCLRRecord` | Implementato |
| MVCC | Multi-Version Concurrency Control. | `Transactions/MVCC.swift` | Implementato (parziale) |
| WAL | Write-Ahead Log: registro delle modifiche prima dei dati. | Parte II, Cap. 5 | Implementato |
| Snapshot | Stato visibile a una transazione MVCC. | `MVCCSnapshot` | Implementato |
| Free Space Map | Struttura per tracciare spazio libero nelle pagine. | `FreeSpaceMap` | Implementato |
| Cost Estimator | Modulo per stimare i costi nel planner. | `CostEstimator` | Implementato |
| Group Commit | Strategia per batch di record WAL. | `groupCommitSync` | Implementato |
