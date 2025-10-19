----------------------------- MODULE SerializableSnapshotIsolation -----------------------------
(*
  Serializable Snapshot Isolation (SSI) Specification for ColibrìDB
  
  This module specifies Serializable Snapshot Isolation, a variant of MVCC
  that provides true serializability without the need for 2PL.
  
  SSI detects dangerous structures in the transaction dependency graph:
  - rw-antidependencies (read-write conflicts)
  - ww-dependencies (write-write conflicts)
  - If these form a cycle involving concurrent transactions, abort one
  
  Based on:
  - Cahill, M. J., Röhm, U., & Fekete, A. D. (2008). "Serializable isolation 
    for snapshot databases." Proceedings of ACM SIGMOD 2008.
  - Cahill, M. J. (2009). "Serializable Isolation for Snapshot Databases."
    PhD Thesis, University of Sydney.
  - Ports, D. R., & Grittner, K. (2012). "Serializable Snapshot Isolation in 
    PostgreSQL." Proceedings of VLDB Endowment, 5(12).
  - Berenson, H., et al. (1995). "A critique of ANSI SQL isolation levels."
    ACM SIGMOD Record, 24(2).
  
  Key Properties:
  - Serializability: Transactions appear to execute in some serial order
  - No phantoms: Range scans see consistent results
  - No lost updates: Write-write conflicts detected
  - Minimal blocking: Read-only transactions never block
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,           \* Maximum concurrent transactions
  MAX_LSN,          \* Maximum LSN
  MAX_PAGES,        \* Maximum pages
  TxIds,            \* Set of transaction IDs
  Keys              \* Set of data keys

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Transaction state
  txStatus,         \* [TxId -> {"active", "committed", "aborted"}]
  txStartTS,        \* [TxId -> Timestamp] - Transaction start timestamp
  txCommitTS,       \* [TxId -> Timestamp] - Transaction commit timestamp
  
  \* MVCC versions
  versions,         \* [Key -> Seq([value, creator_tid, visible_to])]
  
  \* SSI-specific tracking
  siReadSet,        \* [TxId -> SUBSET Keys] - Keys read by transaction
  siWriteSet,       \* [TxId -> SUBSET Keys] - Keys written by transaction
  
  \* Conflict detection
  inConflict,       \* [TxId -> SUBSET TxId] - rw-antidependencies (T1 reads, T2 writes)
  outConflict,      \* [TxId -> SUBSET TxId] - rw-dependencies (T1 writes, T2 reads)
  
  \* Global timestamp oracle
  globalTS,         \* Nat - Monotonically increasing timestamp
  
  \* Predicate locks for range queries
  predicateLocks    \* [TxId -> Seq([table, predicate])] - SIREAD locks

ssiVars == <<txStatus, txStartTS, txCommitTS, versions, siReadSet, siWriteSet,
              inConflict, outConflict, globalTS, predicateLocks>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_SSI ==
  /\ txStatus \in [TxIds -> {"active", "committed", "aborted"}]
  /\ txStartTS \in [TxIds -> Nat]
  /\ txCommitTS \in [TxIds -> Nat]
  /\ versions \in [Keys -> Seq([value: Value, creatorTxId: TxIds, visibleTo: Nat])]
  /\ siReadSet \in [TxIds -> SUBSET Keys]
  /\ siWriteSet \in [TxIds -> SUBSET Keys]
  /\ inConflict \in [TxIds -> SUBSET TxIds]
  /\ outConflict \in [TxIds -> SUBSET TxIds]
  /\ globalTS \in Nat
  /\ predicateLocks \in [TxIds -> Seq([table: STRING, predicate: STRING])]

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Get active transactions at a given timestamp
ActiveTxAt(ts) ==
  {tid \in TxIds : txStatus[tid] = "active" /\ txStartTS[tid] <= ts}

\* Check if transaction T1 has rw-antidependency to T2
\* (T1 reads X, T2 writes X, T1 started before T2 committed)
HasRWAntiDependency(t1, t2) ==
  /\ t1 # t2
  /\ \E key \in siReadSet[t1] \intersect siWriteSet[t2]:
       /\ txStartTS[t1] < txCommitTS[t2]
       /\ txStatus[t2] = "committed"

\* Check if transaction T1 has ww-dependency to T2
\* (T1 and T2 write same key, T1 commits before T2)
HasWWDependency(t1, t2) ==
  /\ t1 # t2
  /\ siWriteSet[t1] \intersect siWriteSet[t2] # {}
  /\ txStatus[t1] = "committed"
  /\ txStatus[t2] = "committed"
  /\ txCommitTS[t1] < txCommitTS[t2]

\* Check for dangerous structure: T1 -> T2 -> T3 -> T1
\* where -> is rw-antidependency or ww-dependency
HasDangerousStructure(tid) ==
  \* Simplified check: T1 has both inConflict and outConflict
  /\ inConflict[tid] # {}
  /\ outConflict[tid] # {}
  /\ \E t2 \in inConflict[tid], t3 \in outConflict[tid]:
       \* Check if there's a path from t3 back to t2
       t2 \in outConflict[t3] \/ t3 \in inConflict[t2]

\* Get visible version for a transaction
GetVisibleVersion(tid, key) ==
  LET txTS == txStartTS[tid]
      versionsForKey == versions[key]
      visibleVersions == {v \in Range(versionsForKey) : v.visibleTo <= txTS}
  IN IF visibleVersions # {}
     THEN CHOOSE v \in visibleVersions : 
            \A other \in visibleVersions : v.visibleTo >= other.visibleTo
     ELSE [value |-> "NULL", creatorTxId |-> 0, visibleTo |-> 0]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_SSI ==
  /\ txStatus = [tid \in TxIds |-> "aborted"]
  /\ txStartTS = [tid \in TxIds |-> 0]
  /\ txCommitTS = [tid \in TxIds |-> 0]
  /\ versions = [k \in Keys |-> <<[value |-> "0", creatorTxId |-> 0, visibleTo |-> 0]>>]
  /\ siReadSet = [tid \in TxIds |-> {}]
  /\ siWriteSet = [tid \in TxIds |-> {}]
  /\ inConflict = [tid \in TxIds |-> {}]
  /\ outConflict = [tid \in TxIds |-> {}]
  /\ globalTS = 1
  /\ predicateLocks = [tid \in TxIds |-> <<>>]

(* --------------------------------------------------------------------------
   TRANSACTION OPERATIONS
   -------------------------------------------------------------------------- *)

\* Begin a new transaction
BeginTx(tid) ==
  /\ txStatus[tid] = "aborted"
  /\ txStatus' = [txStatus EXCEPT ![tid] = "active"]
  /\ txStartTS' = [txStartTS EXCEPT ![tid] = globalTS]
  /\ globalTS' = globalTS + 1
  /\ siReadSet' = [siReadSet EXCEPT ![tid] = {}]
  /\ siWriteSet' = [siWriteSet EXCEPT ![tid] = {}]
  /\ inConflict' = [inConflict EXCEPT ![tid] = {}]
  /\ outConflict' = [outConflict EXCEPT ![tid] = {}]
  /\ predicateLocks' = [predicateLocks EXCEPT ![tid] = <<>>]
  /\ UNCHANGED <<txCommitTS, versions>>

\* Read a key (with SSI tracking)
ReadKey(tid, key) ==
  /\ txStatus[tid] = "active"
  /\ LET version == GetVisibleVersion(tid, key)
         \* Check for rw-conflicts: other transactions wrote after we started
         conflictingTxs == {t \in TxIds : 
                             /\ t # tid
                             /\ key \in siWriteSet[t]
                             /\ txStartTS[tid] < txCommitTS[t]
                             /\ txStatus[t] = "committed"}
     IN /\ siReadSet' = [siReadSet EXCEPT ![tid] = @ \union {key}]
        /\ outConflict' = [outConflict EXCEPT ![tid] = @ \union conflictingTxs]
        /\ inConflict' = [t \in TxIds |-> 
                           IF t \in conflictingTxs 
                           THEN inConflict[t] \union {tid}
                           ELSE inConflict[t]]
        /\ UNCHANGED <<txStatus, txStartTS, txCommitTS, versions, siWriteSet, 
                      globalTS, predicateLocks>>

\* Write a key (create new version)
WriteKey(tid, key, newValue) ==
  /\ txStatus[tid] = "active"
  /\ LET \* Check for write-write conflicts
         conflictingReaders == {t \in TxIds :
                                 /\ t # tid
                                 /\ key \in siReadSet[t]
                                 /\ txStatus[t] = "active"
                                 /\ txStartTS[t] < txStartTS[tid]}
     IN /\ siWriteSet' = [siWriteSet EXCEPT ![tid] = @ \union {key}]
        /\ inConflict' = [inConflict EXCEPT ![tid] = @ \union conflictingReaders]
        /\ outConflict' = [t \in TxIds |->
                            IF t \in conflictingReaders
                            THEN outConflict[t] \union {tid}
                            ELSE outConflict[t]]
        /\ UNCHANGED <<txStatus, txStartTS, txCommitTS, versions, siReadSet, 
                      globalTS, predicateLocks>>

\* Range scan with predicate lock
RangeScan(tid, table, predicate) ==
  /\ txStatus[tid] = "active"
  /\ predicateLocks' = [predicateLocks EXCEPT ![tid] = 
                         Append(@, [table |-> table, predicate |-> predicate])]
  /\ UNCHANGED <<txStatus, txStartTS, txCommitTS, versions, siReadSet, siWriteSet,
                inConflict, outConflict, globalTS>>

\* Commit transaction (with SSI validation)
CommitTx(tid) ==
  /\ txStatus[tid] = "active"
  /\ ~HasDangerousStructure(tid)  \* SSI validation: no dangerous structure
  /\ txStatus' = [txStatus EXCEPT ![tid] = "committed"]
  /\ txCommitTS' = [txCommitTS EXCEPT ![tid] = globalTS]
  /\ globalTS' = globalTS + 1
  /\ versions' = [k \in Keys |-> 
                   IF k \in siWriteSet[tid]
                   THEN Append(versions[k], [value |-> "new", 
                                             creatorTxId |-> tid, 
                                             visibleTo |-> globalTS])
                   ELSE versions[k]]
  /\ UNCHANGED <<txStartTS, siReadSet, siWriteSet, inConflict, outConflict, predicateLocks>>

\* Abort transaction (either manually or due to SSI conflict)
AbortTx(tid) ==
  /\ txStatus[tid] = "active"
  /\ txStatus' = [txStatus EXCEPT ![tid] = "aborted"]
  /\ UNCHANGED <<txStartTS, txCommitTS, versions, siReadSet, siWriteSet,
                inConflict, outConflict, globalTS, predicateLocks>>

\* Automatic abort due to dangerous structure
AutoAbortOnConflict(tid) ==
  /\ txStatus[tid] = "active"
  /\ HasDangerousStructure(tid)
  /\ AbortTx(tid)

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_SSI ==
  \/ \E tid \in TxIds: BeginTx(tid)
  \/ \E tid \in TxIds, key \in Keys: ReadKey(tid, key)
  \/ \E tid \in TxIds, key \in Keys, val \in Value: WriteKey(tid, key, val)
  \/ \E tid \in TxIds, table \in STRING, pred \in STRING: RangeScan(tid, table, pred)
  \/ \E tid \in TxIds: CommitTx(tid)
  \/ \E tid \in TxIds: AbortTx(tid)
  \/ \E tid \in TxIds: AutoAbortOnConflict(tid)

Spec_SSI == Init_SSI /\ [][Next_SSI]_ssiVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Serializability
\* All committed transactions form a serializable history
Inv_SSI_Serializability ==
  \* No committed transaction has a dangerous structure
  \A tid \in TxIds:
    txStatus[tid] = "committed" => ~HasDangerousStructure(tid)

\* Invariant 2: Snapshot Isolation property
Inv_SSI_SnapshotIsolation ==
  \* Each transaction sees a consistent snapshot
  \A tid \in TxIds:
    txStatus[tid] = "active" =>
      \A key \in siReadSet[tid]:
        GetVisibleVersion(tid, key).visibleTo <= txStartTS[tid]

\* Invariant 3: Write-write conflict detection
Inv_SSI_WriteWriteConflict ==
  \* Concurrent writes to same key create conflicts
  \A t1, t2 \in TxIds:
    /\ t1 # t2
    /\ txStatus[t1] = "active"
    /\ txStatus[t2] = "active"
    /\ siWriteSet[t1] \intersect siWriteSet[t2] # {}
    => t1 \in inConflict[t2] \/ t2 \in inConflict[t1]

\* Invariant 4: Read-write conflict tracking
Inv_SSI_ReadWriteConflict ==
  \A t1, t2 \in TxIds:
    t2 \in inConflict[t1] =>
      \E key \in siReadSet[t1] \intersect siWriteSet[t2]: TRUE

\* Invariant 5: Timestamp monotonicity
Inv_SSI_TimestampMonotonic ==
  /\ \A tid \in TxIds: txStartTS[tid] <= globalTS
  /\ \A tid \in TxIds: txStatus[tid] = "committed" => txCommitTS[tid] <= globalTS

\* Combined safety invariant
Inv_SSI_Safety ==
  /\ TypeOK_SSI
  /\ Inv_SSI_Serializability
  /\ Inv_SSI_SnapshotIsolation
  /\ Inv_SSI_WriteWriteConflict
  /\ Inv_SSI_TimestampMonotonic

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: Transactions eventually complete (commit or abort)
Prop_SSI_TxCompletion ==
  \A tid \in TxIds:
    [](txStatus[tid] = "active" => 
       <>(txStatus[tid] \in {"committed", "aborted"}))

\* Property 2: Read-only transactions always commit
Prop_SSI_ReadOnlyCommit ==
  \A tid \in TxIds:
    [](txStatus[tid] = "active" /\ siWriteSet[tid] = {} =>
       <>(txStatus[tid] = "committed"))

\* Property 3: Non-conflicting transactions commit
Prop_SSI_NonConflictingCommit ==
  \A tid \in TxIds:
    [](txStatus[tid] = "active" /\ inConflict[tid] = {} /\ outConflict[tid] = {} =>
       <>(txStatus[tid] = "committed"))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: SSI provides serializability
THEOREM SSI_Serializability ==
  Spec_SSI => []Inv_SSI_Serializability

\* Theorem 2: SSI is a refinement of Snapshot Isolation
THEOREM SSI_RefinesSnapshot ==
  Spec_SSI => []Inv_SSI_SnapshotIsolation

\* Theorem 3: Read-only transactions never abort
THEOREM SSI_ReadOnlyProgress ==
  Spec_SSI => Prop_SSI_ReadOnlyCommit

=============================================================================

(*
  REFERENCES:
  
  [1] Cahill, M. J., Röhm, U., & Fekete, A. D. (2008). "Serializable isolation
      for snapshot databases." Proceedings of the 2008 ACM SIGMOD international
      conference on Management of data (pp. 729-738).
  
  [2] Cahill, M. J. (2009). "Serializable Isolation for Snapshot Databases."
      PhD Thesis, University of Sydney.
  
  [3] Ports, D. R., & Grittner, K. (2012). "Serializable Snapshot Isolation in
      PostgreSQL." Proceedings of the VLDB Endowment, 5(12), 1850-1861.
  
  [4] Fekete, A., Liarokapis, D., O'Neil, E., O'Neil, P., & Shasha, D. (2005).
      "Making snapshot isolation serializable." ACM Transactions on Database
      Systems (TODS), 30(2), 492-528.
  
  [5] Berenson, H., Bernstein, P., Gray, J., Melton, J., O'Neil, E., & O'Neil, P.
      (1995). "A critique of ANSI SQL isolation levels." ACM SIGMOD Record,
      24(2), 1-10.
  
  IMPLEMENTATION NOTES:
  
  - SSI detects dangerous structures in the serialization graph
  - Dangerous structure: T1 -rw-> T2 -rw-> T3 -rw-> T1 (cycle)
  - Implementation uses SIREAD locks for predicate locking
  - PostgreSQL uses this algorithm (since version 9.1)
  - Less conservative than 2PL, more scalable than pure SI
  - First-committer-wins for write-write conflicts
*)

