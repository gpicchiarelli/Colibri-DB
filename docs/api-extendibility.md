# API & Estendibilità

La filosofia "protocol-first" di ColibrìDB permette di estendere funzionalità chiave aggiungendo implementazioni conformi ai protocolli pubblici.

## Storage & indici
- `TableStorageProtocol` — implementa un nuovo motore (es. colonnare) fornendo `insert/scan/read/update/remove` e integrandosi con MVCC/WAL.
- `IndexProtocol` — crea indici personalizzati (es. R-Tree, Bloom-filtered) compatibili con `Database.updateIndexes`.
- `AnyStringIndex` — esempio di factory type-erased per scegliere il backend a runtime.

## WAL
- `WALProtocol` — permette di sostituire `FileWAL` con backend remoti o compressi.
- Le append generano `LSN`: mantenere monotonicità e logging CRC per garantire compatibilità con recovery ARIES.

## Concorrenza
- `LockManagerProtocol` — possibile integrare lock distribuiti o algoritmi alternativi (es. lock-free) purché rispettino le semantiche.
- `TransactionManagerProtocol` — pensato per implementazioni server-side o cluster.

## Policy & ottimizzazione
- `PolicyStoreProtocol` — backend persistente (es. catalogo) o con replica.
- `OptimizationSimulatorProtocol` — sostituibile con modelli ML o cost model avanzati.

## CLI & driver
- La CLI è modulare: basta aggiungere nuovi handler in `Sources/coldb/main.swift` replicando il pattern `handleXYZ`.
- Roadmap: driver Swift async/await (`Codable`) e protocolli remoti (REST/gRPC) potranno riutilizzare gli stessi componenti.

## Best practice
- Aggiungere test dedicati nel package SwiftPM.
- Aggiornare `docs/` descrivendo il nuovo backend/feature.
- Validare l'interoperabilità con MVCC, WAL e buffer pool dove applicabile.
