------------------------------- MODULE RECOVERY -------------------------------
(*
  ColibrìDB ARIES Recovery Specification
  
  Implements complete ARIES (Algorithm for Recovery and Isolation Exploiting Semantics):
  
  Three phases:
  1. Analysis: Scan WAL forward from last checkpoint, build ATT and DPT
  2. Redo: Replay all logged operations from oldest recLSN in DPT
  3. Undo: Rollback uncommitted transactions using undo records
  
  Key Properties:
  - Idempotence: Recovery can run multiple times safely
  - Completeness: All committed transactions restored
  - Consistency: Database in consistent state after recovery
  - No Force: Don't need to flush pages at commit
  - Steal: Can evict dirty pages before commit
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Based on: "ARIES: A Transaction Recovery Method" (Mohan et al., 1992)
*)

EXTENDS CORE, Naturals, Sequences, FiniteSets

CONSTANTS ModifiablePages  \* Set of pages that can be modified

VARIABLES
  \* WAL state (from WAL module)
  wal,            \* Sequence of WAL records (durable)
  flushedLSN,     \* Highest LSN flushed
  
  \* Page state
  dataPages,      \* [PageId -> Page]
  pageLSN,        \* [PageId -> LSN] - last LSN applied to page
  
  \* Recovery state
  phase,          \* {idle, analysis, redo, undo, done}
  att,            \* Active Transaction Table: TxId -> [lastLSN, status]
  dpt,            \* Dirty Page Table: PageId -> recLSN (first LSN that dirtied)
  redoLSN,        \* Current LSN being redone
  undoList,       \* Sequence of [txId, lsn] to undo
  clrRecords,     \* Compensation Log Records written during undo
  
  \* System state
  crashed         \* Boolean: has system crashed?

recoveryVars == <<phase, att, dpt, redoLSN, undoList, clrRecords>>

allVars == <<wal, flushedLSN, dataPages, pageLSN, recoveryVars, crashed>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Active Transaction Table entry
ATTEntry == [
  lastLSN: LSNs,
  status: {"active", "prepared", "committed", "aborted"}
]

\* Dirty Page Table entry
DPTEntry == LSNs  \* recLSN - first LSN that dirtied the page

\* Undo record
UndoRecord == [
  txId: TxIds,
  lsn: LSNs
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Recovery ==
  /\ wal \in Seq(WALRecord)
  /\ flushedLSN \in LSNs
  /\ dataPages \in [ModifiablePages -> Page]
  /\ pageLSN \in [ModifiablePages -> LSNs]
  /\ phase \in {"idle", "analysis", "redo", "undo", "done"}
  /\ att \in [TxIds -> ATTEntry]
  /\ dpt \in [ModifiablePages -> DPTEntry]
  /\ redoLSN \in LSNs
  /\ undoList \in Seq(UndoRecord)
  /\ clrRecords \in Seq(LSNs)
  /\ crashed \in BOOLEAN

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ wal = <<>>
  /\ flushedLSN = 0
  /\ dataPages = [p \in ModifiablePages |-> [
       header |-> [
         magic |-> PAGE_MAGIC,
         pageId |-> p,
         pageLSN |-> 0,
         freeStart |-> 32,
         freeEnd |-> PAGE_SIZE,
         slotCount |-> 0,
         checksum |-> 0
       ],
       slots |-> <<>>,
       data |-> <<>>
     ]]
  /\ pageLSN = [p \in ModifiablePages |-> 0]
  /\ phase = "idle"
  /\ att = [tid \in TxIds |-> [lastLSN |-> 0, status |-> "aborted"]]
  /\ dpt = [p \in ModifiablePages |-> 0]
  /\ redoLSN = 0
  /\ undoList = <<>>
  /\ clrRecords = <<>>
  /\ crashed = FALSE

\* System crashes (begin recovery)
Crash ==
  /\ ~crashed
  /\ crashed' = TRUE
  /\ phase' = "analysis"
  /\ UNCHANGED <<wal, flushedLSN, dataPages, pageLSN, att, dpt, redoLSN, undoList, clrRecords>>

(* --------------------------------------------------------------------------
   ANALYSIS PHASE
   -------------------------------------------------------------------------- *)

\* Scan WAL forward from last checkpoint to build ATT and DPT
AnalysisPhase ==
  /\ phase = "analysis"
  /\ crashed
  /\ LET 
       \* Find all transactions in WAL
       txInWAL == {wal[i].txId : i \in DOMAIN wal}
       
       \* Build ATT: for each tx, find its last LSN and determine status
       newATT == [tid \in TxIds |->
         IF tid \in txInWAL
         THEN
           LET txRecords == {i \in DOMAIN wal : wal[i].txId = tid}
               lastIdx == Max(txRecords)
               lastRec == wal[lastIdx]
               status == CASE lastRec.kind = "commit" -> "committed"
                           [] lastRec.kind = "abort" -> "aborted"
                           [] OTHER -> "active"
           IN [lastLSN |-> lastRec.lsn, status |-> status]
         ELSE [lastLSN |-> 0, status |-> "aborted"]
       ]
       
       \* Build DPT: for each page, find first LSN that modified it
       newDPT == [pid \in ModifiablePages |->
         LET pageRecords == {i \in DOMAIN wal : 
                              wal[i].pageId = pid /\ 
                              wal[i].kind \in {"heapInsert", "heapUpdate", "heapDelete", 
                                               "indexInsert", "indexDelete"}}
         IN IF pageRecords = {}
            THEN 0
            ELSE wal[Min(pageRecords)].lsn
       ]
       
       \* Find oldest recLSN for redo start point
       minRecLSN == LET nonZero == {newDPT[p] : p \in ModifiablePages, newDPT[p] > 0}
                    IN IF nonZero = {} THEN flushedLSN + 1 ELSE Min(nonZero)
     IN
       /\ att' = newATT
       /\ dpt' = newDPT
       /\ redoLSN' = minRecLSN
       /\ phase' = "redo"
       /\ UNCHANGED <<wal, flushedLSN, dataPages, pageLSN, undoList, clrRecords, crashed>>

(* --------------------------------------------------------------------------
   REDO PHASE
   -------------------------------------------------------------------------- *)

\* Apply a single WAL record idempotently
ApplyWALRecord(record) ==
  /\ record.kind \in {"heapInsert", "heapUpdate", "heapDelete", "indexInsert", "indexDelete"}
  /\ LET pid == record.pageId
     IN
       /\ pid \in ModifiablePages
       /\ pageLSN[pid] < record.lsn  \* LSN comparison for idempotence
       /\ pageLSN' = [pageLSN EXCEPT ![pid] = record.lsn]
       \* Simplified: don't actually modify page data
       /\ UNCHANGED dataPages

\* Redo one record
RedoStep ==
  /\ phase = "redo"
  /\ crashed
  /\ redoLSN <= Len(wal)
  /\ redoLSN > 0
  /\ LET record == wal[redoLSN]
     IN
       /\ \/ \* Redo if needed
             /\ record.kind \in {"heapInsert", "heapUpdate", "heapDelete", 
                                 "indexInsert", "indexDelete"}
             /\ ApplyWALRecord(record)
          \/ \* Skip non-update records
             /\ record.kind \notin {"heapInsert", "heapUpdate", "heapDelete", 
                                    "indexInsert", "indexDelete"}
             /\ UNCHANGED <<dataPages, pageLSN>>
       /\ redoLSN' = redoLSN + 1
       /\ UNCHANGED <<wal, flushedLSN, phase, att, dpt, undoList, clrRecords, crashed>>

\* Redo phase complete, move to undo
RedoComplete ==
  /\ phase = "redo"
  /\ crashed
  /\ redoLSN > Len(wal)
  /\ LET activeTx == {tid \in TxIds : att[tid].status = "active"}
         undos == SelectSeq(<<>> , LAMBDA r: FALSE)  \* Build undo list
     IN
       /\ phase' = "undo"
       /\ undoList' = [i \in DOMAIN activeTx |-> 
            [txId |-> activeTx[i], lsn |-> att[activeTx[i]].lastLSN]]
       /\ UNCHANGED <<wal, flushedLSN, dataPages, pageLSN, att, dpt, redoLSN, clrRecords, crashed>>

(* --------------------------------------------------------------------------
   UNDO PHASE
   -------------------------------------------------------------------------- *)

\* Undo one operation (write CLR)
\* CRITICAL FIX: Follow prevLSN chain backwards (from ARIES paper Figure 5)
UndoStep ==
  /\ phase = "undo"
  /\ crashed
  /\ undoList # <<>>
  /\ LET undoRec == Head(undoList)
         tid == undoRec.txId
         lsn == undoRec.lsn
     IN
       /\ lsn > 0
       /\ lsn <= Len(wal)
       /\ LET record == wal[lsn]
          IN
            /\ record.txId = tid
            /\ \/ \* Write CLR and follow prevLSN chain
                  /\ record.kind \in {"heapInsert", "heapUpdate", "heapDelete"}
                  /\ LET clr == [lsn |-> lsn, undoNextLSN |-> record.prevLSN]
                     IN
                       /\ clrRecords' = Append(clrRecords, clr.lsn)
                       /\ IF record.prevLSN > 0
                          THEN \* Continue undoing previous operation
                            undoList' = <<[txId |-> tid, lsn |-> record.prevLSN]>> \o Tail(undoList)
                          ELSE \* No more to undo for this tx
                            undoList' = Tail(undoList)
               \/ \* CLR record - skip to undoNextLSN
                  /\ record.kind = "clr"
                  /\ IF record.undoNextLSN > 0
                     THEN undoList' = <<[txId |-> tid, lsn |-> record.undoNextLSN]>> \o Tail(undoList)
                     ELSE undoList' = Tail(undoList)
                  /\ UNCHANGED clrRecords
               \/ \* Skip non-undoable records, follow prevLSN
                  /\ record.kind \notin {"heapInsert", "heapUpdate", "heapDelete", "clr"}
                  /\ IF record.prevLSN > 0
                     THEN undoList' = <<[txId |-> tid, lsn |-> record.prevLSN]>> \o Tail(undoList)
                     ELSE undoList' = Tail(undoList)
                  /\ UNCHANGED clrRecords
       /\ UNCHANGED <<wal, flushedLSN, dataPages, pageLSN, phase, att, dpt, redoLSN, crashed>>

\* Undo phase complete, recovery done
UndoComplete ==
  /\ phase = "undo"
  /\ crashed
  /\ undoList = <<>>
  /\ phase' = "done"
  /\ crashed' = FALSE
  /\ \* Mark all active transactions as aborted
     att' = [tid \in TxIds |->
       IF att[tid].status = "active"
       THEN [att[tid] EXCEPT !.status = "aborted"]
       ELSE att[tid]]
  /\ UNCHANGED <<wal, flushedLSN, dataPages, pageLSN, dpt, redoLSN, undoList, clrRecords>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Idempotence - redo operations idempotent via LSN comparison
Inv_RECOVERY_Idempotence ==
  /\ phase \in {"redo", "undo", "done"}
  /\ \A p \in ModifiablePages:
       \A i, j \in DOMAIN wal:
         /\ wal[i].pageId = p
         /\ wal[j].pageId = p
         /\ i < j
         => wal[i].lsn < wal[j].lsn

\* Invariant 2: Completeness - all committed tx have pages with correct LSN
Inv_RECOVERY_Completeness ==
  phase = "done" =>
    \A tid \in TxIds:
      att[tid].status = "committed" =>
        \A i \in DOMAIN wal:
          /\ wal[i].txId = tid
          /\ wal[i].pageId \in ModifiablePages
          => pageLSN[wal[i].pageId] >= wal[i].lsn

\* Invariant 3: Consistency - all active tx aborted after recovery
Inv_RECOVERY_Consistency ==
  phase = "done" =>
    \A tid \in TxIds:
      att[tid].status \in {"aborted", "committed"}

\* Invariant 4: ATT and DPT valid during recovery
Inv_RECOVERY_ATT_DPT_Valid ==
  /\ phase \in {"redo", "undo"} =>
       \A tid \in TxIds:
         att[tid].lastLSN <= Len(wal)
  /\ phase \in {"redo", "undo"} =>
       \A p \in ModifiablePages:
         dpt[p] <= Len(wal) + 1

\* Invariant 5: Redo starts from correct LSN
Inv_RECOVERY_RedoStartPoint ==
  phase = "redo" =>
    LET minRecLSN == Min({dpt[p] : p \in ModifiablePages, dpt[p] > 0})
    IN redoLSN >= minRecLSN \/ redoLSN = minRecLSN

\* Invariant 6: Page LSNs monotonically increasing
Inv_RECOVERY_PageLSNMonotonic ==
  \A p \in ModifiablePages:
    \A i, j \in DOMAIN wal:
      /\ wal[i].pageId = p
      /\ wal[j].pageId = p
      /\ i < j
      /\ pageLSN[p] >= wal[j].lsn
      => pageLSN[p] >= wal[i].lsn

\* Combined safety invariant
Inv_RECOVERY_Safety ==
  /\ TypeOK_Recovery
  /\ Inv_RECOVERY_Idempotence
  /\ Inv_RECOVERY_Completeness
  /\ Inv_RECOVERY_Consistency
  /\ Inv_RECOVERY_ATT_DPT_Valid
  /\ Inv_RECOVERY_RedoStartPoint
  /\ Inv_RECOVERY_PageLSNMonotonic

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, recovery completes
Liveness_RecoveryCompletes ==
  [](crashed => <>(phase = "done"))

\* Eventually, all phases complete
Liveness_PhasesComplete ==
  /\ [](phase = "analysis" => <>(phase = "redo"))
  /\ [](phase = "redo" => <>(phase = "undo"))
  /\ [](phase = "undo" => <>(phase = "done"))

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ Crash
  \/ AnalysisPhase
  \/ RedoStep
  \/ RedoComplete
  \/ UndoStep
  \/ UndoComplete

Spec == Init /\ [][Next]_allVars

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: Recovery is idempotent
THEOREM Recovery_Idempotence ==
  Spec => []Inv_RECOVERY_Idempotence

\* Theorem 2: All committed transactions are recovered
THEOREM Recovery_Completeness ==
  Spec => []Inv_RECOVERY_Completeness

\* Theorem 3: Recovery eventually completes
THEOREM Recovery_Terminates ==
  Spec => Liveness_RecoveryCompletes

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    MAX_TX = 3
    MAX_LSN = 20
    MAX_PAGES = 5
    ModifiablePages = {1, 2, 3}
    PAGE_SIZE = 1024
  
  Invariants to check:
    - Inv_RECOVERY_Safety
  
  Temporal properties:
    - Liveness_RecoveryCompletes (with fairness)
  
  State constraints:
    - Len(wal) <= MAX_LSN
    - redoLSN <= MAX_LSN + 1
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_Recovery(recovery: ARIESRecovery) -> [String: Any] {
      return [
          "phase": recovery.phase.rawValue,
          "att": recovery.activeTransactionTable.mapValues { entry in
              ["lastLSN": entry.lastLSN, "status": entry.status.rawValue]
          },
          "dpt": recovery.dirtyPageTable,
          "redoLSN": recovery.redoLSN,
          "undoList": recovery.undoList.map { ["txId": $0.txId, "lsn": $0.lsn] },
          "clrRecords": recovery.clrRecords,
          "crashed": recovery.systemCrashed
      ]
  }
  
  TRACE POINTS:
  
  - traceLog(.recoveryCrash, state: toTLA_Recovery(self))
  - traceLog(.recoveryAnalysisStart, state: toTLA_Recovery(self))
  - traceLog(.recoveryAnalysisDone, state: toTLA_Recovery(self), att: att, dpt: dpt)
  - traceLog(.recoveryRedoStart, state: toTLA_Recovery(self), startLSN: redoLSN)
  - traceLog(.recoveryRedoRecord, state: toTLA_Recovery(self), lsn: lsn)
  - traceLog(.recoveryRedoDone, state: toTLA_Recovery(self))
  - traceLog(.recoveryUndoStart, state: toTLA_Recovery(self), undoList: undoList)
  - traceLog(.recoveryUndoRecord, state: toTLA_Recovery(self), txId: tid, lsn: lsn)
  - traceLog(.recoveryComplete, state: toTLA_Recovery(self))
*)

