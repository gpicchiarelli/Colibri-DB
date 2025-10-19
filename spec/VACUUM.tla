----------------------------- MODULE VACUUM -----------------------------
(*
  VACUUM and Garbage Collection Specification for ColibrìDB
  
  This module specifies the garbage collection of dead tuples and obsolete MVCC versions.
  It implements:
  - Dead tuple identification and collection
  - MVCC version chain cleanup
  - Index cleanup (remove pointers to dead tuples)
  - Page defragmentation and space reclamation
  - Statistics update during vacuum
  - VACUUM FULL (table rewrite)
  - Autovacuum threshold calculation
  
  Based on:
  - Stonebraker, M. (1987). "The design of the POSTGRES storage system."
    Proceedings of VLDB 1987.
  - PostgreSQL Documentation: "Chapter 25. Routine Database Maintenance Tasks."
    https://www.postgresql.org/docs/current/maintenance.html
  - Bernstein, P. A., & Goodman, N. (1983). "Multiversion concurrency control
    - Theory and algorithms." ACM Transactions on Database Systems, 8(4).
  - Larson, P. Å., et al. (2011). "High-Performance Concurrency Control Mechanisms
    for Main-Memory Databases." Proceedings of VLDB 2011.
  - Graefe, G. (2007). "Hierarchical locking in B-tree indexes." BTW 2007.
  
  Key Properties:
  - Space reclamation: Dead tuples eventually removed
  - Correctness: Only remove tuples invisible to all transactions
  - Non-blocking: Concurrent operations allowed
  - Index consistency: Indexes updated after tuple removal
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,                  \* From CORE
  MAX_LSN,                 \* From CORE
  MAX_PAGES,               \* From CORE
  Tables,                  \* Set of table names
  VACUUM_THRESHOLD,        \* Percentage of dead tuples to trigger autovacuum
  MAX_DEAD_TUPLES          \* Maximum dead tuples before forced vacuum

(* --------------------------------------------------------------------------
   TUPLE VISIBILITY
   -------------------------------------------------------------------------- *)

\* Tuple state
TupleState == {
  "live",          \* Visible to some transactions
  "dead",          \* Invisible to all transactions, can be removed
  "recently_dead"  \* Invisible to all active txs, but visible to some snapshots
}

\* Tuple with MVCC metadata
Tuple == [
  tid: RID,
  data: STRING,
  xmin: TxId,          \* Transaction that created this version
  xmax: TxId,          \* Transaction that deleted this version (0 if not deleted)
  state: TupleState
]

\* Vacuum statistics
VacuumStats == [
  numScanned: Nat,       \* Tuples scanned
  numRemoved: Nat,       \* Dead tuples removed
  numDead: Nat,          \* Dead tuples found
  pagesScanned: Nat,     \* Pages scanned
  pagesFreed: Nat,       \* Pages completely freed
  indexScans: Nat        \* Number of index cleanup scans
]

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Table storage
  heapTuples,           \* [Tables -> SUBSET Tuple] - All tuples in each table
  deadTuples,           \* [Tables -> SUBSET RID] - Dead tuple IDs
  freespace,            \* [Tables -> [PageId -> Nat]] - Free space per page
  
  \* Index state
  indexPointers,        \* [Tables -> [RID -> PageId]] - Index entries
  
  \* Transaction visibility
  oldestXmin,           \* TxId - Oldest transaction that can see any tuple
  recentXmin,           \* TxId - Oldest active transaction
  
  \* Vacuum state
  vacuumInProgress,     \* [Tables -> BOOLEAN] - Vacuum running on table
  vacuumPhase,          \* [Tables -> {"scan", "clean", "index", "truncate", "done"}]
  vacuumStats,          \* [Tables -> VacuumStats] - Statistics per table
  
  \* Autovacuum state
  autovacuumEnabled,    \* BOOLEAN - Autovacuum enabled
  deadTupleCount,       \* [Tables -> Nat] - Current dead tuple count
  totalTupleCount,      \* [Tables -> Nat] - Total tuple count
  lastVacuum,           \* [Tables -> Nat] - Timestamp of last vacuum
  
  \* VACUUM FULL state
  rewriteInProgress,    \* [Tables -> BOOLEAN] - Table rewrite in progress
  shadowTable           \* [Tables -> SUBSET Tuple] - Shadow table for rewrite

vacuumVars == <<heapTuples, deadTuples, freespace, indexPointers, oldestXmin,
                recentXmin, vacuumInProgress, vacuumPhase, vacuumStats,
                autovacuumEnabled, deadTupleCount, totalTupleCount, lastVacuum,
                rewriteInProgress, shadowTable>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_VACUUM ==
  /\ heapTuples \in [Tables -> SUBSET Tuple]
  /\ deadTuples \in [Tables -> SUBSET RID]
  /\ freespace \in [Tables -> [PageIds -> Nat]]
  /\ indexPointers \in [Tables -> [RID -> PageIds]]
  /\ oldestXmin \in TxIds
  /\ recentXmin \in TxIds
  /\ vacuumInProgress \in [Tables -> BOOLEAN]
  /\ vacuumPhase \in [Tables -> {"scan", "clean", "index", "truncate", "done", "none"}]
  /\ vacuumStats \in [Tables -> VacuumStats]
  /\ autovacuumEnabled \in BOOLEAN
  /\ deadTupleCount \in [Tables -> Nat]
  /\ totalTupleCount \in [Tables -> Nat]
  /\ lastVacuum \in [Tables -> Nat]
  /\ rewriteInProgress \in [Tables -> BOOLEAN]
  /\ shadowTable \in [Tables -> SUBSET Tuple]

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Check if a tuple is visible to the oldest transaction
IsTupleVisible(tuple, xmin) ==
  /\ tuple.xmin < xmin
  /\ (tuple.xmax = 0 \/ tuple.xmax >= xmin)

\* Check if a tuple is dead (invisible to all transactions)
IsTupleDead(tuple) ==
  /\ tuple.xmax # 0
  /\ tuple.xmax < oldestXmin

\* Calculate dead tuple percentage
DeadTuplePercentage(table) ==
  IF totalTupleCount[table] = 0
  THEN 0
  ELSE (deadTupleCount[table] * 100) \div totalTupleCount[table]

\* Check if autovacuum should trigger
ShouldAutovacuum(table) ==
  /\ autovacuumEnabled
  /\ ~vacuumInProgress[table]
  /\ DeadTuplePercentage(table) >= VACUUM_THRESHOLD

\* Get tuples on a page
TuplesOnPage(table, pageId) ==
  {t \in heapTuples[table] : t.tid \div 100 = pageId}  \* Simplified mapping

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_VACUUM ==
  /\ heapTuples = [t \in Tables |-> {}]
  /\ deadTuples = [t \in Tables |-> {}]
  /\ freespace = [t \in Tables |-> [p \in PageIds |-> PAGE_SIZE]]
  /\ indexPointers = [t \in Tables |-> [rid \in {} |-> 0]]
  /\ oldestXmin = 1
  /\ recentXmin = 1
  /\ vacuumInProgress = [t \in Tables |-> FALSE]
  /\ vacuumPhase = [t \in Tables |-> "none"]
  /\ vacuumStats = [t \in Tables |-> 
                     [numScanned |-> 0, numRemoved |-> 0, numDead |-> 0,
                      pagesScanned |-> 0, pagesFreed |-> 0, indexScans |-> 0]]
  /\ autovacuumEnabled = TRUE
  /\ deadTupleCount = [t \in Tables |-> 0]
  /\ totalTupleCount = [t \in Tables |-> 0]
  /\ lastVacuum = [t \in Tables |-> 0]
  /\ rewriteInProgress = [t \in Tables |-> FALSE]
  /\ shadowTable = [t \in Tables |-> {}]

(* --------------------------------------------------------------------------
   TUPLE OPERATIONS (CREATE DEAD TUPLES)
   -------------------------------------------------------------------------- *)

\* Insert a tuple
InsertTuple(table, tuple) ==
  /\ heapTuples' = [heapTuples EXCEPT ![table] = @ \union {tuple}]
  /\ totalTupleCount' = [totalTupleCount EXCEPT ![table] = @ + 1]
  /\ indexPointers' = [indexPointers EXCEPT ![table][tuple.tid] = tuple.tid \div 100]
  /\ UNCHANGED <<deadTuples, freespace, oldestXmin, recentXmin, vacuumInProgress,
                vacuumPhase, vacuumStats, autovacuumEnabled, deadTupleCount,
                lastVacuum, rewriteInProgress, shadowTable>>

\* Delete a tuple (mark as deleted, creates dead tuple)
DeleteTuple(table, tid, deletingTxId) ==
  /\ \E tuple \in heapTuples[table]: tuple.tid = tid
  /\ LET oldTuple == CHOOSE t \in heapTuples[table]: t.tid = tid
         newTuple == [oldTuple EXCEPT !.xmax = deletingTxId, !.state = "recently_dead"]
     IN /\ heapTuples' = [heapTuples EXCEPT ![table] = (@ \ {oldTuple}) \union {newTuple}]
        /\ deadTupleCount' = [deadTupleCount EXCEPT ![table] = @ + 1]
        /\ UNCHANGED <<deadTuples, freespace, indexPointers, oldestXmin, recentXmin,
                      vacuumInProgress, vacuumPhase, vacuumStats, autovacuumEnabled,
                      totalTupleCount, lastVacuum, rewriteInProgress, shadowTable>>

\* Update oldestXmin (oldest transaction that can see any data)
UpdateOldestXmin(newXmin) ==
  /\ oldestXmin' = newXmin
  /\ \* Mark recently_dead tuples as dead if now invisible to all
     heapTuples' = [t \in Tables |->
                     {IF tuple.state = "recently_dead" /\ tuple.xmax < newXmin
                      THEN [tuple EXCEPT !.state = "dead"]
                      ELSE tuple : tuple \in heapTuples[t]}]
  /\ UNCHANGED <<deadTuples, freespace, indexPointers, recentXmin, vacuumInProgress,
                vacuumPhase, vacuumStats, autovacuumEnabled, deadTupleCount,
                totalTupleCount, lastVacuum, rewriteInProgress, shadowTable>>

(* --------------------------------------------------------------------------
   VACUUM PHASES
   -------------------------------------------------------------------------- *)

\* Phase 1: Start VACUUM on a table
StartVacuum(table) ==
  /\ ~vacuumInProgress[table]
  /\ vacuumInProgress' = [vacuumInProgress EXCEPT ![table] = TRUE]
  /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "scan"]
  /\ vacuumStats' = [vacuumStats EXCEPT ![table] = 
                      [numScanned |-> 0, numRemoved |-> 0, numDead |-> 0,
                       pagesScanned |-> 0, pagesFreed |-> 0, indexScans |-> 0]]
  /\ UNCHANGED <<heapTuples, deadTuples, freespace, indexPointers, oldestXmin,
                recentXmin, autovacuumEnabled, deadTupleCount, totalTupleCount,
                lastVacuum, rewriteInProgress, shadowTable>>

\* Phase 2: Scan heap and identify dead tuples
ScanHeap(table) ==
  /\ vacuumPhase[table] = "scan"
  /\ LET deadInTable == {t.tid : t \in heapTuples[table], IsTupleDead(t)}
     IN /\ deadTuples' = [deadTuples EXCEPT ![table] = deadInTable]
        /\ vacuumStats' = [vacuumStats EXCEPT ![table].numScanned = Cardinality(heapTuples[table]),
                                             ![table].numDead = Cardinality(deadInTable)]
        /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "clean"]
        /\ UNCHANGED <<heapTuples, freespace, indexPointers, oldestXmin, recentXmin,
                      vacuumInProgress, autovacuumEnabled, deadTupleCount,
                      totalTupleCount, lastVacuum, rewriteInProgress, shadowTable>>

\* Phase 3: Remove dead tuples from heap
CleanHeap(table) ==
  /\ vacuumPhase[table] = "clean"
  /\ LET deadTids == deadTuples[table]
         liveTuples == {t \in heapTuples[table] : t.tid \notin deadTids}
     IN /\ heapTuples' = [heapTuples EXCEPT ![table] = liveTuples]
        /\ deadTupleCount' = [deadTupleCount EXCEPT ![table] = 0]
        /\ vacuumStats' = [vacuumStats EXCEPT ![table].numRemoved = Cardinality(deadTids)]
        /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "index"]
        /\ UNCHANGED <<deadTuples, freespace, indexPointers, oldestXmin, recentXmin,
                      vacuumInProgress, autovacuumEnabled, totalTupleCount,
                      lastVacuum, rewriteInProgress, shadowTable>>

\* Phase 4: Clean up index pointers to removed tuples
CleanIndexes(table) ==
  /\ vacuumPhase[table] = "index"
  /\ LET deadTids == deadTuples[table]
         newPointers == [rid \in DOMAIN indexPointers[table] \ deadTids |-> 
                          indexPointers[table][rid]]
     IN /\ indexPointers' = [indexPointers EXCEPT ![table] = newPointers]
        /\ vacuumStats' = [vacuumStats EXCEPT ![table].indexScans = 1]
        /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "truncate"]
        /\ UNCHANGED <<heapTuples, deadTuples, freespace, oldestXmin, recentXmin,
                      vacuumInProgress, autovacuumEnabled, deadTupleCount,
                      totalTupleCount, lastVacuum, rewriteInProgress, shadowTable>>

\* Phase 5: Truncate empty pages at end of table
TruncateTable(table) ==
  /\ vacuumPhase[table] = "truncate"
  /\ LET emptyPages == {p \in PageIds : TuplesOnPage(table, p) = {}}
     IN /\ freespace' = [freespace EXCEPT ![table] = 
                          [p \in DOMAIN @ |-> IF p \in emptyPages THEN PAGE_SIZE ELSE @[p]]]
        /\ vacuumStats' = [vacuumStats EXCEPT ![table].pagesFreed = Cardinality(emptyPages)]
        /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "done"]
        /\ UNCHANGED <<heapTuples, deadTuples, indexPointers, oldestXmin, recentXmin,
                      vacuumInProgress, autovacuumEnabled, deadTupleCount,
                      totalTupleCount, lastVacuum, rewriteInProgress, shadowTable>>

\* Phase 6: Finish VACUUM
FinishVacuum(table, timestamp) ==
  /\ vacuumPhase[table] = "done"
  /\ vacuumInProgress' = [vacuumInProgress EXCEPT ![table] = FALSE]
  /\ vacuumPhase' = [vacuumPhase EXCEPT ![table] = "none"]
  /\ lastVacuum' = [lastVacuum EXCEPT ![table] = timestamp]
  /\ deadTuples' = [deadTuples EXCEPT ![table] = {}]
  /\ UNCHANGED <<heapTuples, freespace, indexPointers, oldestXmin, recentXmin,
                vacuumStats, autovacuumEnabled, deadTupleCount, totalTupleCount,
                rewriteInProgress, shadowTable>>

(* --------------------------------------------------------------------------
   AUTOVACUUM
   -------------------------------------------------------------------------- *)

\* Autovacuum triggers automatically
AutovacuumTrigger(table) ==
  /\ ShouldAutovacuum(table)
  /\ StartVacuum(table)

\* Enable/disable autovacuum
SetAutovacuum(enabled) ==
  /\ autovacuumEnabled' = enabled
  /\ UNCHANGED <<heapTuples, deadTuples, freespace, indexPointers, oldestXmin,
                recentXmin, vacuumInProgress, vacuumPhase, vacuumStats,
                deadTupleCount, totalTupleCount, lastVacuum, rewriteInProgress,
                shadowTable>>

(* --------------------------------------------------------------------------
   VACUUM FULL (TABLE REWRITE)
   -------------------------------------------------------------------------- *)

\* Start VACUUM FULL (rewrites entire table)
StartVacuumFull(table) ==
  /\ ~rewriteInProgress[table]
  /\ ~vacuumInProgress[table]
  /\ rewriteInProgress' = [rewriteInProgress EXCEPT ![table] = TRUE]
  /\ shadowTable' = [shadowTable EXCEPT ![table] = 
                      {t \in heapTuples[table] : t.state = "live"}]
  /\ UNCHANGED <<heapTuples, deadTuples, freespace, indexPointers, oldestXmin,
                recentXmin, vacuumInProgress, vacuumPhase, vacuumStats,
                autovacuumEnabled, deadTupleCount, totalTupleCount, lastVacuum>>

\* Finish VACUUM FULL (atomic switch)
FinishVacuumFull(table) ==
  /\ rewriteInProgress[table]
  /\ heapTuples' = [heapTuples EXCEPT ![table] = shadowTable[table]]
  /\ deadTupleCount' = [deadTupleCount EXCEPT ![table] = 0]
  /\ totalTupleCount' = [totalTupleCount EXCEPT ![table] = Cardinality(shadowTable[table])]
  /\ rewriteInProgress' = [rewriteInProgress EXCEPT ![table] = FALSE]
  /\ shadowTable' = [shadowTable EXCEPT ![table] = {}]
  /\ UNCHANGED <<deadTuples, freespace, indexPointers, oldestXmin, recentXmin,
                vacuumInProgress, vacuumPhase, vacuumStats, autovacuumEnabled, lastVacuum>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_VACUUM ==
  \/ \E table \in Tables, tuple \in Tuple: InsertTuple(table, tuple)
  \/ \E table \in Tables, tid \in RID, txId \in TxIds: DeleteTuple(table, tid, txId)
  \/ \E xmin \in TxIds: UpdateOldestXmin(xmin)
  \/ \E table \in Tables: StartVacuum(table)
  \/ \E table \in Tables: ScanHeap(table)
  \/ \E table \in Tables: CleanHeap(table)
  \/ \E table \in Tables: CleanIndexes(table)
  \/ \E table \in Tables: TruncateTable(table)
  \/ \E table \in Tables, ts \in Nat: FinishVacuum(table, ts)
  \/ \E table \in Tables: AutovacuumTrigger(table)
  \/ \E enabled \in BOOLEAN: SetAutovacuum(enabled)
  \/ \E table \in Tables: StartVacuumFull(table)
  \/ \E table \in Tables: FinishVacuumFull(table)

Spec_VACUUM == Init_VACUUM /\ [][Next_VACUUM]_vacuumVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Dead tuples are eventually removed
Inv_VACUUM_DeadRemoved ==
  \A table \in Tables:
    vacuumPhase[table] = "none" => deadTuples[table] = {}

\* Invariant 2: Only dead tuples are removed
Inv_VACUUM_CorrectRemoval ==
  \A table \in Tables:
    vacuumPhase[table] = "clean" =>
      \A tid \in deadTuples[table]:
        \E t \in heapTuples[table]: t.tid = tid /\ IsTupleDead(t)

\* Invariant 3: Index consistency after cleanup
Inv_VACUUM_IndexConsistency ==
  \A table \in Tables:
    vacuumPhase[table] = "none" =>
      \A rid \in DOMAIN indexPointers[table]:
        \E t \in heapTuples[table]: t.tid = rid

\* Invariant 4: VACUUM doesn't run concurrently with VACUUM FULL
Inv_VACUUM_NoConflict ==
  \A table \in Tables:
    vacuumInProgress[table] => ~rewriteInProgress[table]

\* Invariant 5: Dead tuple count is accurate
Inv_VACUUM_DeadCountAccurate ==
  \A table \in Tables:
    vacuumPhase[table] = "none" =>
      deadTupleCount[table] = Cardinality({t \in heapTuples[table] : t.state = "dead"})

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: VACUUM eventually completes
Prop_VACUUM_Completion ==
  \A table \in Tables:
    [](vacuumInProgress[table] => <>(vacuumPhase[table] = "done"))

\* Property 2: Autovacuum eventually triggers when threshold exceeded
Prop_VACUUM_AutovacuumTriggers ==
  \A table \in Tables:
    [](ShouldAutovacuum(table) => <>(vacuumInProgress[table]))

\* Property 3: Dead tuples eventually removed
Prop_VACUUM_EventualCleanup ==
  \A table \in Tables:
    [](Cardinality(deadTuples[table]) > 0 => <>StartVacuum(table))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM VACUUM_Correctness ==
  Spec_VACUUM => []Inv_VACUUM_CorrectRemoval

THEOREM VACUUM_Progress ==
  Spec_VACUUM => Prop_VACUUM_Completion

=============================================================================

(*
  REFERENCES:
  
  [1] Stonebraker, M. (1987). "The design of the POSTGRES storage system."
      Proceedings of the 13th International Conference on Very Large Data Bases.
  
  [2] PostgreSQL Global Development Group. "Chapter 25. Routine Database Maintenance
      Tasks." PostgreSQL Documentation.
      https://www.postgresql.org/docs/current/maintenance.html
  
  [3] Bernstein, P. A., & Goodman, N. (1983). "Multiversion concurrency control -
      Theory and algorithms." ACM Transactions on Database Systems (TODS), 8(4).
  
  [4] Larson, P. Å., Blanas, S., Diaconu, C., Freedman, C., Patel, J. M., &
      Zwilling, M. (2011). "High-Performance Concurrency Control Mechanisms for
      Main-Memory Databases." Proceedings of the VLDB Endowment, 5(4).
  
  [5] Graefe, G. (2007). "Hierarchical locking in B-tree indexes." BTW 2007.
  
  IMPLEMENTATION NOTES:
  
  - VACUUM removes dead tuples not visible to any transaction
  - Autovacuum runs when dead tuple % exceeds threshold (typically 20%)
  - VACUUM FULL rewrites entire table, reclaims maximum space
  - Index cleanup removes pointers to dead tuples
  - Truncate reclaims empty pages at end of table
  - Similar to PostgreSQL VACUUM, Oracle's Automatic Segment Space Management
*)

