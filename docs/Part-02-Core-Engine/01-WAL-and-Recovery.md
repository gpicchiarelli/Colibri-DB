# Capitolo 5 — Write-Ahead Logging e Recupero ARIES

## 5.1 Fondamenti teorici
Il Write-Ahead Log (WAL) garantisce durabilità e atomicità: ogni modifica è registrata su un log sequenziale prima di essere applicata ai dati. L'algoritmo ARIES (Algorithms for Recovery and Isolation Exploiting Semantics) introduce tre fasi: Analisi, REDO, UNDO. Presentiamo formalmente gli invarianti principali:
- Ordine totale degli LSN e monotonicità.
- WAL-before-data: `pageLSN` non supera `flushedLSN`.
- Idempotenza del REDO e compensazioni nel UNDO.

## 5.2 Implementazione in `FileWALManager`
`FileWALManager` implementa le interfacce `WALWriter`, `WALReader`, `WALCheckpointing`.

### 5.2.1 Append sincronizzato
La funzione `append(_:)` assegna un nuovo LSN (`_nextLSN`) e appende il record al buffer. Descriviamo la sequenza:
1. Lock su `lsnLock` per garantire atomicità nella generazione LSN.
2. Scrittura nel buffer `pendingRecords`.
3. Eventuale trigger di flush se il batch supera soglie.

### 5.2.2 Flush e group commit
`flushPendingRecords()` scrive su disco un batch ottimizzato. Spieghiamo il ruolo del `GroupCommitOptimizer` e misuriamo la latenza (`metrics`).

## 5.3 Checkpoint
`Database.checkpoint()` sincronizza WAL, heap e indici e salva `CheckpointCatalog`. `FileWALManager.writeCheckpoint` produce un `WALCheckpointRecord` contenente DPT e ATT. Analizziamo la serializzazione e l'impatto sulla lunghezza del log.

## 5.4 Recovery
### 5.4.1 Analisi (`analysisPhase`)
Ricostruisce ATT e DPT iterando il WAL. Gli invarianti:
- ATT contiene `txId -> lastLSN` per transazioni ancora aperte.
- DPT contiene `pageId -> recLSN` per pagine sporche al crash.

### 5.4.2 REDO (`redoPhase`)
Si riprocessano i record dalla `recLSN` minima. La funzione `shouldRedo` verifica `pageLSN` per idempotenza.

### 5.4.3 UNDO (`undoPhase`)
Si percorrono le transazioni attive in ordine decrescente di LSN, emettendo CLRs. L'algoritmo termina quando `undoNextLSN` raggiunge 0.

## 5.5 Compensating Log Records
`WALCLRRecord` incapsula l'azione inversa. Analizziamo il campo `UndoAction` e come `redoCLR` garantisca idempotenza.

## 5.6 Dimostrazione empirica
Esperimento:
1. Eseguire transazioni e forzare un crash (kill server).
2. Riavviare e osservare `replayGlobalWAL()`.
3. Registrare lo stato di ATT/DPT a ogni fase.

## 5.7 Verifica formale
Argomentiamo perché la combinazione di invarianti e algoritmi implementati assicura ACID, facendo riferimento ai lemmi di ARIES e alla corrispondente implementazione.
