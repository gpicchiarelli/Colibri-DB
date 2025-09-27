# Glossario

- **ACID** — Atomicità, Consistenza, Isolamento, Durabilità.
- **MVCC** — Multi-Version Concurrency Control; mantiene versioni multiple delle tuple per letture non bloccanti.
- **WAL** — Write-Ahead Logging; log su disco scritto prima dei dati per garantire recovery.
- **LSN** — Log Sequence Number; identificatore monotono dei record WAL.
- **Checkpoint** — Snapshot consistente di dati e WAL per accelerare recovery.
- **Actor (Swift)** — Unità di isolamento concorrente in Swift Concurrency.
- **Multiplexing** — Molte connessioni logiche su poche connessioni fisiche.
- **Volcano** — Modello di esecuzione iterator-based (open/next/close) per operatori di query.
- **FSM (Free Space Map)** — Mappa che traccia lo spazio libero per pagina nel heap file.
- **RID** — Record Identifier (pageId + slotId) di una riga nel heap.
- **CLR** — Compensation Log Record, record WAL utilizzato durante UNDO.
- **DPT** — Dirty Page Table, tabella delle pagine sporche con LSN minimo da redo.
- **PITR** — Point-in-Time Recovery.
