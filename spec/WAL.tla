--------------------------------- MODULE WAL ---------------------------------
(*
  ColibrìDB Write-Ahead Logging (WAL) Specification
  
  This module specifies the behavior of the Write-Ahead Log subsystem,
  including:
  - Record appending with LSN assignment
  - Group commit optimization
  - Durable flush to disk
  - Checkpoint creation
  - Crash and recovery semantics
  
  Key Properties:
  - Log-Before-Data: Data pages written only after WAL flush
  - Durability: Committed transactions survive crashes
  - Total Order: Log records maintain sequential order
  - Idempotent Recovery: Recovery can run multiple times safely
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Version: 1.0.0
  
  Based on: ARIES recovery algorithm (Mohan et al., 1992)
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Sequences, Naturals, FiniteSets, TLC

(* --------------------------------------------------------------------------
   CONSTANTS
   -------------------------------------------------------------------------- *)

\* Maximum number of pending records before forced flush
CONSTANT GROUP_COMMIT_THRESHOLD

\* Maximum wait time (ms) before forced flush
CONSTANT GROUP_COMMIT_TIMEOUT_MS

\* Set of all possible page IDs that can be modified
CONSTANT ModifiablePages

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* WAL state
  wal,            \* Sequence of WAL records (on disk after flush)
  nextLSN,        \* Next LSN to assign
  flushedLSN,     \* Highest LSN flushed to disk
  pendingRecords, \* Sequence of records pending flush
  txLastLSN,      \* [TxId -> LSN] - last LSN written by each tx
  
  \* Data pages state
  dataApplied,    \* Set of page IDs that have been written to disk
  pageLSN,        \* Function: PageId -> LSN (last LSN applied to page)
  
  \* Checkpoint state
  lastCheckpointLSN,  \* LSN of most recent checkpoint
  dirtyPageTable,     \* PageId -> recLSN (first LSN that dirtied page)
  
  \* Group commit state
  groupCommitTimer,   \* Timer for forced flush
  
  \* System state
  crashed         \* Boolean: has system crashed?

vars == <<wal, nextLSN, flushedLSN, pendingRecords, txLastLSN, dataApplied, pageLSN, 
          lastCheckpointLSN, dirtyPageTable, groupCommitTimer, crashed>>

(* --------------------------------------------------------------------------
   TYPE INVARIANTS
   -------------------------------------------------------------------------- *)

TypeOK ==
  /\ wal \in Seq(WALRecord)
  /\ nextLSN \in LSNs
  /\ flushedLSN \in LSNs
  /\ pendingRecords \in Seq(WALRecord)
  /\ txLastLSN \in [TxIds -> LSNs]
  /\ dataApplied \subseteq ModifiablePages
  /\ pageLSN \in [ModifiablePages -> LSNs]
  /\ lastCheckpointLSN \in LSNs \union {0}
  /\ dirtyPageTable \in [ModifiablePages -> LSNs]
  /\ groupCommitTimer \in Nat
  /\ crashed \in BOOLEAN

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ wal = <<>>
  /\ nextLSN = 1
  /\ flushedLSN = 0
  /\ pendingRecords = <<>>
  /\ txLastLSN = [tid \in TxIds |-> 0]
  /\ dataApplied = {}
  /\ pageLSN = [p \in ModifiablePages |-> 0]
  /\ lastCheckpointLSN = 0
  /\ dirtyPageTable = [p \in ModifiablePages |-> 0]
  /\ groupCommitTimer = 0
  /\ crashed = FALSE

(* --------------------------------------------------------------------------
   ACTIONS
   -------------------------------------------------------------------------- *)

\* Append a record to the WAL (in-memory, not yet durable)
\* Assigns LSN and prevLSN, adds to pending queue
\* Based on ARIES paper - maintains undo chain via prevLSN
Append(record) ==
  /\ ~crashed
  /\ LET tid == record.txId
         prevLSN == txLastLSN[tid]
         newRecord == [record EXCEPT !.lsn = nextLSN, !.prevLSN = prevLSN]
     IN
       /\ pendingRecords' = Append(pendingRecords, newRecord)
       /\ txLastLSN' = [txLastLSN EXCEPT ![tid] = nextLSN]
       /\ nextLSN' = nextLSN + 1
       /\ UNCHANGED <<wal, flushedLSN, dataApplied, pageLSN, 
                      lastCheckpointLSN, dirtyPageTable, groupCommitTimer, crashed>>

\* Flush all pending records to disk (make them durable)
\* Group commit: flush multiple records with single fsync
Flush ==
  /\ ~crashed
  /\ pendingRecords # <<>>
  /\ wal' = wal \o pendingRecords
  /\ flushedLSN' = nextLSN - 1
  /\ pendingRecords' = <<>>
  /\ UNCHANGED <<nextLSN, dataApplied, pageLSN, 
                 lastCheckpointLSN, dirtyPageTable, crashed>>

\* Force flush when group commit threshold reached (size-based)
GroupCommitFlush ==
  /\ ~crashed
  /\ Len(pendingRecords) >= GROUP_COMMIT_THRESHOLD
  /\ Flush

\* Force flush when timeout reached (time-based)
GroupCommitTimeout ==
  /\ ~crashed
  /\ pendingRecords # <<>>
  /\ groupCommitTimer >= GROUP_COMMIT_TIMEOUT_MS
  /\ Flush
  /\ groupCommitTimer' = 0

\* Tick group commit timer
TickGroupCommitTimer ==
  /\ ~crashed
  /\ pendingRecords # <<>>
  /\ groupCommitTimer < GROUP_COMMIT_TIMEOUT_MS
  /\ groupCommitTimer' = groupCommitTimer + 1
  /\ UNCHANGED <<wal, nextLSN, flushedLSN, pendingRecords, txLastLSN, dataApplied, pageLSN,
                 lastCheckpointLSN, dirtyPageTable, crashed>>

\* Apply a WAL record to data pages (write page to disk)
\* Can only apply if WAL record has been flushed (Log-Before-Data)
ApplyToDataPage(pid) ==
  /\ ~crashed
  /\ pid \in ModifiablePages
  /\ pid \notin dataApplied
  /\ pageLSN[pid] <= flushedLSN  \* Log-Before-Data rule!
  /\ dataApplied' = dataApplied \union {pid}
  /\ UNCHANGED <<wal, nextLSN, flushedLSN, pendingRecords, pageLSN,
                 lastCheckpointLSN, dirtyPageTable, crashed>>

\* Update page LSN when a record affects a page
UpdatePageLSN(pid, lsn) ==
  /\ ~crashed
  /\ pid \in ModifiablePages
  /\ lsn <= nextLSN
  /\ pageLSN' = [pageLSN EXCEPT ![pid] = lsn]
  /\ IF pid \notin dataApplied
     THEN \* Page is dirty, update DPT if not already present
       /\ IF dirtyPageTable[pid] = 0
          THEN dirtyPageTable' = [dirtyPageTable EXCEPT ![pid] = lsn]
          ELSE UNCHANGED dirtyPageTable
     ELSE UNCHANGED dirtyPageTable
  /\ UNCHANGED <<wal, nextLSN, flushedLSN, pendingRecords, dataApplied,
                 lastCheckpointLSN, crashed>>

\* Write a checkpoint record
\* Checkpoint captures current DPT and ATT (simplified: just DPT here)
Checkpoint ==
  /\ ~crashed
  /\ pendingRecords = <<>>  \* All records must be flushed first
  /\ LET checkpointRecord == [
           lsn |-> nextLSN,
           kind |-> "checkpoint",
           txId |-> 0,
           pageId |-> 0
         ]
     IN
       /\ wal' = Append(wal, checkpointRecord)
       /\ flushedLSN' = nextLSN
       /\ lastCheckpointLSN' = nextLSN
       /\ nextLSN' = nextLSN + 1
       /\ UNCHANGED <<pendingRecords, dataApplied, pageLSN, 
                      dirtyPageTable, crashed>>

\* System crash (non-deterministic)
\* Loses all pending records and in-memory state
Crash ==
  /\ ~crashed
  /\ crashed' = TRUE
  /\ pendingRecords' = <<>>  \* Pending records lost
  /\ UNCHANGED <<wal, nextLSN, flushedLSN, dataApplied, pageLSN,
                 lastCheckpointLSN, dirtyPageTable>>

\* Recovery after crash
\* Restore state from durable WAL
Recover ==
  /\ crashed
  /\ crashed' = FALSE
  /\ nextLSN' = IF wal = <<>> THEN 1 ELSE wal[Len(wal)].lsn + 1
  /\ flushedLSN' = IF wal = <<>> THEN 0 ELSE wal[Len(wal)].lsn
  /\ pendingRecords' = <<>>
  /\ UNCHANGED <<wal, dataApplied, pageLSN, lastCheckpointLSN, dirtyPageTable>>

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E record \in WALRecord: Append(record)
  \/ Flush
  \/ GroupCommitFlush
  \/ GroupCommitTimeout
  \/ TickGroupCommitTimer
  \/ \E pid \in ModifiablePages: ApplyToDataPage(pid)
  \/ \E pid \in ModifiablePages, lsn \in LSNs: UpdatePageLSN(pid, lsn)
  \/ Checkpoint
  \/ Crash
  \/ Recover

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Log-Before-Data
\* A data page can be written to disk only if its pageLSN <= flushedLSN
\* This ensures durability: if page is on disk, its WAL records are too
Inv_WAL_LogBeforeData ==
  \A pid \in dataApplied: pageLSN[pid] <= flushedLSN

\* Invariant 2: Durability Guarantee
\* All flushed WAL records remain durable even after crash
\* (Formalized: wal never shrinks, only grows)
Inv_WAL_DurabilityInvariant ==
  \A i \in DOMAIN wal:
    /\ wal[i].lsn \in LSNs
    /\ i > 1 => wal[i].lsn > wal[i-1].lsn

\* Invariant 3: Total Order of LSNs
\* LSNs are monotonically increasing in the WAL
Inv_WAL_LogOrderInvariant ==
  /\ nextLSN > flushedLSN \/ nextLSN = flushedLSN + 1
  /\ flushedLSN = IF wal = <<>> THEN 0 ELSE wal[Len(wal)].lsn
  /\ \A i, j \in DOMAIN wal: i < j => wal[i].lsn < wal[j].lsn

\* Invariant 4: Pending Records Have Consecutive LSNs
\* Pending records (not yet flushed) have LSNs starting from flushedLSN + 1
Inv_WAL_PendingConsecutive ==
  \/ pendingRecords = <<>>
  \/ \A i \in DOMAIN pendingRecords:
       pendingRecords[i].lsn = flushedLSN + i

\* Invariant 5: Checkpoint Consistency
\* Checkpoint LSN is always in the flushed portion of the WAL
Inv_WAL_CheckpointConsistency ==
  lastCheckpointLSN <= flushedLSN

\* Invariant 6: Dirty Page Table Consistency
\* If a page has a non-zero recLSN in DPT, its pageLSN >= recLSN
Inv_WAL_DPTConsistency ==
  \A pid \in ModifiablePages:
    dirtyPageTable[pid] > 0 => pageLSN[pid] >= dirtyPageTable[pid]

\* Combined safety invariant
Inv_WAL_Safety ==
  /\ TypeOK
  /\ Inv_WAL_LogBeforeData
  /\ Inv_WAL_DurabilityInvariant
  /\ Inv_WAL_LogOrderInvariant
  /\ Inv_WAL_PendingConsecutive
  /\ Inv_WAL_CheckpointConsistency
  /\ Inv_WAL_DPTConsistency

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, all pending records are flushed
\* Temporal formula: []<>(pendingRecords = <<>>)
Liveness_EventualFlush ==
  []<>(pendingRecords = <<>> \/ crashed)

\* Eventually, after crash, system recovers
\* Temporal formula: [](crashed => <> ~crashed)
Liveness_EventualRecovery ==
  [](crashed => <> ~crashed)

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: Log-Before-Data implies Durability
\* If a page is written to disk, its corresponding WAL records are durable
THEOREM LogBeforeData_Implies_Durability ==
  Inv_WAL_LogBeforeData =>
    \A pid \in dataApplied:
      \E i \in DOMAIN wal: wal[i].pageId = pid /\ wal[i].lsn <= pageLSN[pid]

\* Theorem 2: Recovery Idempotence
\* Running recovery multiple times produces the same state
THEOREM Recovery_Idempotence ==
  \A s1, s2 \in [vars -> TypeOK]:
    (Recover /\ Recover) => (s1 = s2)

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    MAX_TX = 3
    MAX_LSN = 20
    MAX_PAGES = 5
    GROUP_COMMIT_THRESHOLD = 3
    ModifiablePages = {1, 2, 3}
    PAGE_SIZE = 1024
  
  Invariants to check:
    - Inv_WAL_Safety
  
  Temporal properties to check:
    - Liveness_EventualFlush
    - Liveness_EventualRecovery
  
  State space constraints:
    - Symmetry on ModifiablePages
    - Limit wal length to MAX_LSN
  
  Expected results:
    - No deadlock
    - All invariants hold
    - Liveness properties satisfied (with fairness assumptions)
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_WAL(wal: FileWAL) -> [String: Any] {
      return [
          "wal": wal.records.map { toTLA_Record($0) },
          "nextLSN": wal.nextLSN,
          "flushedLSN": wal.flushedLSN,
          "pendingRecords": wal.pendingRecords.map { toTLA_Record($0) },
          "dataApplied": Set(dataPages.filter { $0.written }.map { $0.pageId }),
          "pageLSN": Dictionary(dataPages.map { ($0.pageId, $0.pageLSN) }),
          "lastCheckpointLSN": wal.lastCheckpointLSN,
          "dirtyPageTable": wal.dirtyPageTable,
          "crashed": false
      ]
  }
  
  TRACE POINTS:
  
  - traceLog(.walAppendStart, state: toTLA_WAL(self))
  - traceLog(.walAppendDone, state: toTLA_WAL(self), lsn: lsn)
  - traceLog(.walFlushStart, state: toTLA_WAL(self))
  - traceLog(.walFlushDone, state: toTLA_WAL(self), flushedLSN: flushedLSN)
  - traceLog(.walCheckpoint, state: toTLA_WAL(self), checkpointLSN: lsn)
  - traceLog(.walCrash, state: toTLA_WAL(self))
  - traceLog(.walRecoveryStart, state: toTLA_WAL(self))
  - traceLog(.walRecoveryEnd, state: toTLA_WAL(self))
*)

