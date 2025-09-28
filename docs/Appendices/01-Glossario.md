# Appendice A — Glossario Tecnico

| Termine | Definizione | Riferimento | Stato |
|---------|-------------|-------------|-------|
| ATT (Active Transaction Table) | Tabella delle transazioni attive usata in ARIES; mappa `txId -> lastLSN`. | `Database+GlobalWALRecovery.swift`, `WALCheckpointRecord`. | Implementato |
| DPT (Dirty Page Table) | Traccia pagine sporche con `recLSN`. | `analysisPhase` | Implementato |
| LSN (Log Sequence Number) | Identificatore monotono del WAL. | `FileWALManager`, `WALRecord.lsn`. | Implementato |
| CLR (Compensation Log Record) | Record WAL generato durante undo. | `WALCLRRecord` | Implementato |
| MVCC | Multi-Version Concurrency Control. | `Transactions/MVCC.swift` | Implementato (parziale) |
