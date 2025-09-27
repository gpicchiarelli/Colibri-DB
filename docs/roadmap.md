# Roadmap

La roadmap è derivata dal piano dettagliato in `TODO.md`. Qui è organizzata per orizzonte temporale e macro area.

## Breve termine (MVP++)
- Completare operatori Volcano (scan, filter, project, join base).
- Estendere parser SQL al DDL/DML minimo (CREATE/ALTER/DROP, INSERT/UPDATE/DELETE).
- Migliorare il coverage dei test unitari per indici (split/merge/borrow, ART range, fuzz WAL).
- Esportare metriche aggiuntive (latency transaction, throughput import/export).
- Integrazione iniziale con Instruments (`os_log`, signpost) per tracing.

## Medio termine
- Ottimizzatore cost-based con statistiche di cardinalità e istogrammi.
- Query parallele multi-thread/actor e pipeline vectorized per workload analitici.
- Replica WAL streaming, backup incrementali e PITR completo.
- Policy load-based con monitoraggio runtime (QPS, CPU) e storicizzazione dei job.
- Cifratura a riposo (AES-GCM) con gestione chiavi sicura.

## Lungo termine
- Server remoto basato su SwiftNIO con autenticazione, autorizzazione e auditing.
- Sharding/partizionamento (hash/range/list) e coordinamento 2PC distribuito.
- Supporto nativo a tipi JSON/documento e operatori analitici avanzati (window functions, materialized view caching).
- Integrazione con driver ufficiali (Swift, gRPC/REST) e pooling connessioni.
- Ottimizzazioni Apple Silicon avanzate (NEON intrinsics, compressione hardware, Secure Enclave per cifratura).

Aggiornare questa roadmap quando si completano gli elementi o vengono introdotte nuove priorità. Per un elenco granularrissimo delle attività consultare `TODO.md`.
