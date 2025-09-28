# Capitolo 9 — Concorrenza, MVCC e Versioning

## 9.1 Motivazioni
MVCC (Multi-Version Concurrency Control) consente letture non bloccanti mantenendo versioni storiche delle tuple. Discutiamo i limiti dei lock esclusivi e i fenomeni isolati da MVCC (dirty read, non-repeatable read).

## 9.2 Strutture dati
- `MVCCManager`: mantiene `activeTIDs`, `visibleTransaction(tid:)`.
- `VersionChain`: catena di versioni per ogni `RID`.
- `Snapshot`: rappresenta la visibilità di un'operazione.

## 9.3 Operazioni
- `registerRead(table:rid:tid:)`: determina se una versione è visibile.
- `registerWrite(table:rid:tid:)`: crea una nuova versione (con timestamp `tid`).
- `commit(tid:)`: marca le versioni come definitive.
- `abort(tid:)`: ripristina versioni precedenti.

## 9.4 Garbage collection
Vecchie versioni vengono rimosse quando non più visibili a nessuna transazione. Il GC scorre la catena e verifica `minActiveTid`.

## 9.5 Integrazione con WAL
Le operazioni MVCC generano record WAL per garantire undo e durabilità. I CLR registrano le versioni ripristinate.

## 9.6 Laboratorio
- Creare due transazioni simultanee per osservare snapshot isolati.
- Verificare fenomeni di phantom e la necessità di ulteriori meccanismi.

## 9.7 Roadmap
- Implementare `Serializable Snapshot Isolation`.
- Locking a granularità fine per operazioni non MVCC.
