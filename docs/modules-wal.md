# WAL & Recovery

Il Write-Ahead Log è la spina dorsale della durabilità in ColibrìDB. Tutte le modifiche persistenti vengono rese stabili sul WAL prima di toccare le pagine dati o gli indici, consentendo recovery crash-safe.

## Formato WAL (DB)
- Header file: magic `CBDW` + versione `u16` (v2).
- Record v2: `CRC32 u32 | type u8 | LSN u64 | prevLSN u64 | pageId u64 | len u32 | payload`. Il bit 7 di `type` indica payload compresso, i bit 6-5 codificano l'algoritmo (`00` = none, `01` = LZFSE, `10` = zlib).
- Tipi supportati: `insertRow`, `deleteRid`, `checkpoint`, `begin`, `commit`, `abort`, `insertPre`, `insertDone`, `deleteRow`, `clr`.
- Ogni append calcola CRC32 sull'intero record e sincronizza tramite `FileHandle.synchronize()` (fsync). Con `walCompression` attivo il payload viene compresso (prefisso da lunghezza originale `u32`).

## Integrazione con le operazioni
1. `insert` emette `insertPre` (row JSON) e `insertDone` (RID) così da garantire idempotenza in caso di crash intermedio.
2. `delete` produce un record con RID e snapshot della riga per facilitare UNDO.
3. `commit/abort` registrano la chiusura della transazione; `rollback` genera Compensation Log Records (CLR) per mantenere la proprietà redo/undo.
4. `checkpoint` forza flush di tabelle/indici e tronca il WAL riducendo il tempo di recovery.

## Dirty Page Table & PageLSN
- `Database.dpt` tiene traccia delle pagine sporche (`pageId → recLSN`).
- Ogni pagina heap e B+Tree mantiene `pageLSN`; durante il redo, se `pageLSN ≥ recordLSN` l'operazione è già applicata.

## WAL per gli indici B+Tree
- Ogni `FileBPlusTreeIndex` ha un WAL dedicato (`.wal`) con header `CBWL` e checkpoint periodici (`checkpointEvery = 256`).
- I record comprendono insert/delete di chiavi, aggiornamenti alle foglie e checkpoint che memorizzano `checkpointLSN` nell'header dell'indice.
- `replayWAL()` viene eseguito all'avvio per riportare l'indice a uno stato consistente prima di accettare nuove operazioni.

## Recovery
- All'avvio `Database` esegue `replayDBWAL()` che:
  1. Legge tutti i record, valida il CRC.
  2. Applica redo per insert/delete seguendo l'ordine LSN.
  3. Per le transazioni incomplete esegue undo inverso tramite catene `prevLSN`.
  4. Aggiorna MVCC e tabelle in modo idempotente.
- Gli indici B+Tree ripetono la stessa procedura (redo + eventuale undo) tramite `FileBPlusTreeIndex.replayWAL()`.

## Strumenti CLI
```
\checkpoint          # flush + truncate WAL DB e indici
\index validate      # controlla coerenza logica
\index dump-header   # ispeziona pageLSN, sibling, occupancy
```

## Roadmap
- Persistenza della Dirty Page Table e del Transaction Table nel checkpoint per ridurre ulteriormente il tempo di recovery.
- Limitazione dei fsync (group commit) attraverso batching configurabile.
- Cifratura dei record WAL e firma autenticata.
