# Capitolo 5 — Write-Ahead Logging e Recupero ARIES

## 5.1 Panoramica del WAL globale
Questa sezione introduce il sottosistema WAL implementato in `Sources/ColibriCore/WAL`. Spiegheremo come `FileWALManager` incapsula le interfacce `WALWriter`, `WALReader` e `WALCheckpointing`, descrivendo attributi (`dbId`, `durabilityMode`, `metrics`) e funzioni principali (`append`, `iterate`, `groupCommitSync`). Verrà illustrato il formato binario dei record partendo da `WALRecord` e `WALKind`.

## 5.2 Sequenza di append
Analizzeremo la catena di chiamate dalla funzione di alto livello (`Database.logHeapInsert`) alla persistenza fisica:
1. `Database.logHeapInsert` crea un `WALHeapInsertRecord` (file `Database+GlobalWAL.swift`).
2. `FileWALManager.append` assegna un LSN incrementale e inserisce il record nella coda di group commit.
3. `FileWALManager.flushPendingRecords` e `groupCommitSync` scrivono il batch su disco.
Ogni passo sarà corredato di diagrammi di flusso, precondizioni, errori possibili e test collegati.

## 5.3 Checkpoint
Descriveremo la procedura `Database.checkpoint()` (file `Database+Checkpoint.swift`) che sincronizza il WAL, i file heap (`FileHeapTable.flush`) e gli indici (`FileBPlusTreeIndex.checkpointIndex`). Mostreremo come `FileWALManager.writeCheckpoint(dpt:att:)` crea un `WALCheckpointRecord` serializzando Dirty Page Table e Active Transaction Table. Ci sarà un esempio di JSON generato da `CheckpointIO.save`.

## 5.4 Recovery ARIES
Vedremo in dettaglio `Database.replayGlobalWAL()` e le tre fasi:
- **Analisi** (`analysisPhase`): inizializzazione dei dizionari `activeTransactionTable` e `dirtyPageTable`; iterazione dei record via `FileWALManager.iterate`.
- **REDO** (`redoPhase`): logica `shouldRedo`, accesso a `FileHeapTable`/`FileBPlusTreeIndex`, gestione PageLSN.
- **UNDO** (`undoPhase`, `undoTransaction`): ricostruzione cronologia transazione, generazione dei CLR.
Per ogni funzione forniremo:
- firma, descrizione, pseudocodice commentato;
- estratti del codice con rimandi alle strutture dati (`RID`, `Row`, `tablesFile`);
- esempi passo-passo con LSN reali.

## 5.5 Compensating Log Records (CLR)
Spiegheremo la struttura `WALCLRRecord` e il campo `UndoAction`. L’analisi includerà la generazione dei CLR nelle funzioni `Database.undoHeapInsert`, `undoHeapUpdate`, `undoHeapDelete` e come questi record vengono trattati durante `redoCLR`.

## 5.6 Esempio completo
Un caso di studio seguirà un crash simulato:
- Stato iniziale del database;
- Sequenza di operazioni e LSN;
- Crash point, dump del WAL;
- Esecuzione di `replayGlobalWAL` con tabelle per ATT/DPT a ogni fase;
- Stato finale verificato con query.
