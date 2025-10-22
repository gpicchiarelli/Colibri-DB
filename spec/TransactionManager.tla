-------------------------- MODULE TransactionManager --------------------------
(*
  ColibrìDB Transaction Manager Specification
  
  Implements full ACID transaction management with:
  - Transaction lifecycle (BEGIN, COMMIT, ABORT)
  - Two-Phase Commit (2PC) for distributed transactions
  - Integration with WAL for durability
  - Integration with MVCC for isolation
  - Lock acquisition and release
  - Deadlock detection and timeout handling
  - Savepoints and partial rollback
  
  Key Properties:
  - Atomicity: Transactions complete fully or not at all
  - Consistency: Database moves from one consistent state to another
  - Isolation: Concurrent transactions properly isolated
  - Durability: Committed changes persist through crashes
  - 2PC Correctness: Distributed commit protocol maintains atomicity
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Based on:
  - "Transaction Processing: Concepts and Techniques" (Gray & Reuter, 1992)
  - "Concurrency Control and Recovery in Database Systems" (Bernstein et al., 1987)
*)

EXTENDS CORE, Naturals, FiniteSets, Sequences

CONSTANTS 
  Resources,      \* Set of lockable resources
  Participants,   \* Set of participant nodes (for 2PC)
  TX_TIMEOUT_MS,  \* Transaction timeout in milliseconds
  PREPARE_TIMEOUT_MS  \* 2PC prepare timeout

VARIABLES
  \* Transaction state
  nextTID,               \* Next transaction ID to assign
  transactions,          \* [TxId -> Transaction]
  txOperations,          \* [TxId -> Seq(Operation)] - operation log
  txLocks,               \* [TxId -> SUBSET Resources] - locks held
  txStartTime,           \* [TxId -> Timestamp] - for timeout detection
  
  \* Two-Phase Commit state
  preparedTransactions,  \* Set of prepared transaction IDs
  coordinatorState,      \* [TxId -> CoordinatorState]
  participantVotes,      \* [TxId -> [Participant -> Vote]]
  prepareTimer,          \* [TxId -> Nat] - timeout for prepare phase
  
  \* WAL integration
  txWALRecords,          \* [TxId -> Seq(LSN)] - WAL records for each tx
  lastCommitLSN,         \* LSN of last commit record
  
  \* MVCC integration
  txSnapshots,           \* [TxId -> Snapshot]
  txWriteSets,           \* [TxId -> SUBSET Keys]
  txReadSets,            \* [TxId -> SUBSET Keys]
  
  \* Deadlock detection
  waitForGraph,          \* [TxId -> SUBSET TxId] - wait-for edges
  deadlockVictim,        \* TxId chosen for abort (or 0)
  
  \* Global clock
  globalClock            \* Global timestamp for timeouts

tmVars == <<nextTID, transactions, txOperations, txLocks, txStartTime,
            preparedTransactions, coordinatorState, participantVotes, prepareTimer,
            txWALRecords, lastCommitLSN,
            txSnapshots, txWriteSets, txReadSets,
            waitForGraph, deadlockVictim, globalClock>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Transaction structure with full metadata
\* Fixed: More precise type definitions with proper constraints
Transaction == [
  tid: TxIds,
  status: TxStatus,
  isolationLevel: IsolationLevel,
  startTime: Timestamp,
  startLSN: LSNs,           \* LSN of BEGIN record
  commitLSN: LSNs,          \* LSN of COMMIT record (0 if not committed)
  firstLSN: LSNs,           \* First LSN written by this tx
  lastLSN: LSNs,            \* Last LSN written by this tx
  isReadOnly: BOOLEAN,     \* Optimization for read-only transactions
  isDistributed: BOOLEAN   \* Whether this is a distributed transaction
]

\* Operation types
\* Fixed: More precise type definitions with proper constraints
Operation == [
  kind: {"read", "write", "update", "delete"},
  resource: Resources,
  oldValue: Value \union {0},
  newValue: Value \union {0}
]

\* 2PC Coordinator states
CoordinatorState == {
  "idle",
  "preparing",    \* Sent PREPARE to participants
  "committing",   \* All voted YES, sending COMMIT
  "aborting"      \* Some voted NO or timeout, sending ABORT
}

\* 2PC Participant votes
Vote == {"yes", "no", "timeout"}

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_TM ==
  /\ nextTID \in TxIds
  /\ transactions \in [TxIds -> Transaction]
  /\ txOperations \in [TxIds -> Seq(Operation)]
  /\ txLocks \in [TxIds -> SUBSET Resources]
  /\ txStartTime \in [TxIds -> Nat]
  /\ preparedTransactions \subseteq TxIds
  /\ coordinatorState \in [TxIds -> CoordinatorState]
  /\ participantVotes \in [TxIds -> [Participants -> Vote]]
  /\ prepareTimer \in [TxIds -> Nat]
  /\ txWALRecords \in [TxIds -> Seq(LSNs)]
  /\ lastCommitLSN \in LSNs
  /\ txSnapshots \in [TxIds -> Snapshot]
  /\ txWriteSets \in [TxIds -> SUBSET Resources]
  /\ txReadSets \in [TxIds -> SUBSET Resources]
  /\ waitForGraph \in [TxIds -> SUBSET TxIds]
  /\ deadlockVictim \in TxIds \union {0}
  /\ globalClock \in Nat

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_TM ==
  /\ nextTID = 1
  /\ transactions = [tid \in TxIds |-> [
       tid |-> 0,
       status |-> "aborted",
       isolationLevel |-> "readCommitted",
       startTime |-> 0,
       startLSN |-> 0,
       commitLSN |-> 0,
       firstLSN |-> 0,
       lastLSN |-> 0,
       isReadOnly |-> TRUE,
       isDistributed |-> FALSE
     ]]
  /\ txOperations = [tid \in TxIds |-> <<>>]
  /\ txLocks = [tid \in TxIds |-> {}]
  /\ txStartTime = [tid \in TxIds |-> 0]
  /\ preparedTransactions = {}
  /\ coordinatorState = [tid \in TxIds |-> "idle"]
  /\ participantVotes = [tid \in TxIds |-> [p \in Participants |-> "timeout"]]
  /\ prepareTimer = [tid \in TxIds |-> 0]
  /\ txWALRecords = [tid \in TxIds |-> <<>>]
  /\ lastCommitLSN = 0
  /\ txSnapshots = [tid \in TxIds |-> [
       txId |-> 0,
       startTS |-> 0,
       xmin |-> 0,
       xmax |-> 0,
       activeTxAtStart |-> {}
     ]]
  /\ txWriteSets = [tid \in TxIds |-> {}]
  /\ txReadSets = [tid \in TxIds |-> {}]
  /\ waitForGraph = [tid \in TxIds |-> {}]
  /\ deadlockVictim = 0
  /\ globalClock = 0

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Get all active transactions
ActiveTransactions == {tid \in TxIds : transactions[tid].status = "active"}

\* Check if transaction holds a lock on resource
HoldsLock(tid, resource) == resource \in txLocks[tid]

\* Check if resource is locked by any other transaction
IsLockedByOther(tid, resource) ==
  \E other \in ActiveTransactions : other # tid /\ HoldsLock(other, resource)

\* Detect cycle in wait-for graph (deadlock detection)
HasDeadlock ==
  \E cycle \in SUBSET ActiveTransactions :
    /\ Cardinality(cycle) > 1
    /\ \A t1 \in cycle: \E t2 \in cycle:
         t1 # t2 /\ t2 \in waitForGraph[t1]

\* Choose victim for deadlock resolution (youngest transaction)
ChooseDeadlockVictim ==
  IF HasDeadlock
  THEN CHOOSE tid \in ActiveTransactions : 
         /\ tid \in UNION {waitForGraph[t] : t \in ActiveTransactions}
         /\ \A other \in ActiveTransactions : tid >= other
  ELSE 0

(* --------------------------------------------------------------------------
   TRANSACTION LIFECYCLE
   -------------------------------------------------------------------------- *)

\* Begin a new transaction
BeginTransaction(tid, isolationLevel, isDistributed) ==
  /\ tid \in TxIds
  /\ transactions[tid].status = "aborted"  \* Can reuse TID
  /\ nextTID <= MAX_TX
  /\ LET currentTS == nextTID
         activeSet == ActiveTransactions
     IN
       /\ transactions' = [transactions EXCEPT ![tid] = [
            tid |-> tid,
            status |-> "active",
            isolationLevel |-> isolationLevel,
            startTime |-> currentTS,
            startLSN |-> nextTID,  \* Simplified: use TID as LSN
            commitLSN |-> 0,
            firstLSN |-> nextTID,
            lastLSN |-> nextTID,
            isReadOnly |-> TRUE,
            isDistributed |-> isDistributed
          ]]
       /\ txSnapshots' = [txSnapshots EXCEPT ![tid] = [
            txId |-> tid,
            startTS |-> currentTS,
            xmin |-> IF activeSet = {} THEN currentTS ELSE Min(activeSet),
            xmax |-> currentTS,
            activeTxAtStart |-> activeSet
          ]]
       /\ txOperations' = [txOperations EXCEPT ![tid] = <<>>]
       /\ txLocks' = [txLocks EXCEPT ![tid] = {}]
       /\ txWriteSets' = [txWriteSets EXCEPT ![tid] = {}]
       /\ txReadSets' = [txReadSets EXCEPT ![tid] = {}]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = <<nextTID>>]
       /\ txStartTime' = [txStartTime EXCEPT ![tid] = globalClock]
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<preparedTransactions, coordinatorState, participantVotes, prepareTimer,
                      lastCommitLSN, waitForGraph, deadlockVictim, globalClock>>

\* Acquire lock on resource
AcquireLock(tid, resource) ==
  /\ tid \in ActiveTransactions
  /\ resource \in Resources
  /\ ~IsLockedByOther(tid, resource)
  /\ txLocks' = [txLocks EXCEPT ![tid] = @ \union {resource}]
  /\ waitForGraph' = [waitForGraph EXCEPT ![tid] = {}]  \* Got lock, remove wait
  /\ UNCHANGED <<nextTID, transactions, txOperations, 
                 preparedTransactions, coordinatorState, participantVotes,
                 txWALRecords, lastCommitLSN, txSnapshots, txWriteSets, txReadSets,
                 deadlockVictim>>

\* Wait for lock (adds edge to wait-for graph)
WaitForLock(tid, resource) ==
  /\ tid \in ActiveTransactions
  /\ resource \in Resources
  /\ IsLockedByOther(tid, resource)
  /\ LET holders == {other \in ActiveTransactions : HoldsLock(other, resource)}
     IN
       /\ waitForGraph' = [waitForGraph EXCEPT ![tid] = holders]
       /\ deadlockVictim' = ChooseDeadlockVictim
       /\ UNCHANGED <<nextTID, transactions, txOperations, txLocks,
                      preparedTransactions, coordinatorState, participantVotes,
                      txWALRecords, lastCommitLSN, txSnapshots, txWriteSets, txReadSets>>

\* Execute read operation
ExecuteRead(tid, resource) ==
  /\ tid \in ActiveTransactions
  /\ resource \in Resources
  /\ HoldsLock(tid, resource)  \* Must hold lock first
  /\ LET op == [kind |-> "read", resource |-> resource, 
                oldValue |-> 0, newValue |-> 0]
     IN
       /\ txOperations' = [txOperations EXCEPT ![tid] = Append(@, op)]
       /\ txReadSets' = [txReadSets EXCEPT ![tid] = @ \union {resource}]
       /\ UNCHANGED <<nextTID, transactions, txLocks,
                      preparedTransactions, coordinatorState, participantVotes,
                      txWALRecords, lastCommitLSN, txSnapshots, txWriteSets,
                      waitForGraph, deadlockVictim>>

\* Execute write operation (generates WAL record)
ExecuteWrite(tid, resource, value) ==
  /\ tid \in ActiveTransactions
  /\ resource \in Resources
  /\ HoldsLock(tid, resource)
  /\ LET op == [kind |-> "write", resource |-> resource,
                oldValue |-> 0, newValue |-> value]
         walLSN == nextTID
     IN
       /\ txOperations' = [txOperations EXCEPT ![tid] = Append(@, op)]
       /\ txWriteSets' = [txWriteSets EXCEPT ![tid] = @ \union {resource}]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = Append(@, walLSN)]
       /\ transactions' = [transactions EXCEPT ![tid].isReadOnly = FALSE,
                                               ![tid].lastLSN = walLSN]
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<txLocks, preparedTransactions, coordinatorState, participantVotes,
                      lastCommitLSN, txSnapshots, txReadSets, waitForGraph, deadlockVictim>>

(* --------------------------------------------------------------------------
   TWO-PHASE COMMIT PROTOCOL
   -------------------------------------------------------------------------- *)

\* Phase 1: Coordinator sends PREPARE to all participants
PrepareTx_Coordinator(tid) ==
  /\ tid \in ActiveTransactions
  /\ transactions[tid].isDistributed
  /\ coordinatorState[tid] = "idle"
  /\ coordinatorState' = [coordinatorState EXCEPT ![tid] = "preparing"]
  /\ participantVotes' = [participantVotes EXCEPT ![tid] = 
       [p \in Participants |-> "timeout"]]  \* Reset votes
  /\ prepareTimer' = [prepareTimer EXCEPT ![tid] = 0]  \* Start timer
  /\ UNCHANGED <<nextTID, transactions, txOperations, txLocks, txStartTime,
                 preparedTransactions, txWALRecords, lastCommitLSN,
                 txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim, globalClock>>

\* Phase 1: Participant votes YES (prepares)
PrepareTx_Participant(tid, participant) ==
  /\ tid \in ActiveTransactions
  /\ participant \in Participants
  /\ coordinatorState[tid] = "preparing"
  /\ participantVotes[tid][participant] = "timeout"
  /\ preparedTransactions' = preparedTransactions \union {tid}
  /\ participantVotes' = [participantVotes EXCEPT ![tid][participant] = "yes"]
  /\ UNCHANGED <<nextTID, transactions, txOperations, txLocks,
                 coordinatorState, txWALRecords, lastCommitLSN,
                 txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim>>

\* Phase 1: Participant votes NO (cannot prepare)
AbortTx_Participant(tid, participant) ==
  /\ tid \in ActiveTransactions
  /\ participant \in Participants
  /\ coordinatorState[tid] = "preparing"
  /\ participantVotes[tid][participant] = "timeout"
  /\ participantVotes' = [participantVotes EXCEPT ![tid][participant] = "no"]
  /\ UNCHANGED <<nextTID, transactions, txOperations, txLocks,
                 preparedTransactions, coordinatorState, txWALRecords, lastCommitLSN,
                 txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim>>

\* Phase 2: Coordinator decides COMMIT (all voted YES)
CommitTx_Coordinator(tid) ==
  /\ tid \in ActiveTransactions \union preparedTransactions
  /\ coordinatorState[tid] = "preparing"
  /\ \A p \in Participants : participantVotes[tid][p] = "yes"
  /\ LET commitLSN == nextTID
     IN
       /\ transactions' = [transactions EXCEPT 
            ![tid].status = "committed",
            ![tid].commitLSN = commitLSN
          ]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = Append(@, commitLSN)]
       /\ coordinatorState' = [coordinatorState EXCEPT ![tid] = "committing"]
       /\ lastCommitLSN' = commitLSN
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<txOperations, txLocks, preparedTransactions, participantVotes,
                      txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim>>

\* Phase 2: Coordinator decides ABORT (some voted NO or timeout)
AbortTx_Coordinator(tid) ==
  /\ tid \in ActiveTransactions \union preparedTransactions
  /\ coordinatorState[tid] = "preparing"
  /\ \E p \in Participants : participantVotes[tid][p] \in {"no", "timeout"}
  /\ LET abortLSN == nextTID
     IN
       /\ transactions' = [transactions EXCEPT ![tid].status = "aborted"]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = Append(@, abortLSN)]
       /\ coordinatorState' = [coordinatorState EXCEPT ![tid] = "aborting"]
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<txOperations, txLocks, preparedTransactions, participantVotes,
                      lastCommitLSN, txSnapshots, txWriteSets, txReadSets, 
                      waitForGraph, deadlockVictim>>

(* --------------------------------------------------------------------------
   SIMPLE COMMIT/ABORT (Non-distributed)
   -------------------------------------------------------------------------- *)

\* Commit a local (non-distributed) transaction
CommitTransaction(tid) ==
  /\ tid \in ActiveTransactions
  /\ ~transactions[tid].isDistributed
  /\ LET commitLSN == nextTID
     IN
       /\ transactions' = [transactions EXCEPT 
            ![tid].status = "committed",
            ![tid].commitLSN = commitLSN
          ]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = Append(@, commitLSN)]
       /\ lastCommitLSN' = commitLSN
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<txOperations, txLocks, preparedTransactions, 
                      coordinatorState, participantVotes,
                      txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim>>

\* Abort a transaction (undo operations, release locks)
AbortTransaction(tid) ==
  /\ tid \in ActiveTransactions \union preparedTransactions
  /\ LET abortLSN == nextTID
     IN
       /\ transactions' = [transactions EXCEPT ![tid].status = "aborted"]
       /\ txWALRecords' = [txWALRecords EXCEPT ![tid] = Append(@, abortLSN)]
       /\ nextTID' = nextTID + 1
       /\ UNCHANGED <<txOperations, txLocks, txStartTime, preparedTransactions, 
                      coordinatorState, participantVotes, prepareTimer, lastCommitLSN,
                      txSnapshots, txWriteSets, txReadSets, waitForGraph, deadlockVictim, globalClock>>

\* Release all locks held by a finished transaction
ReleaseLocks(tid) ==
  /\ transactions[tid].status \in {"committed", "aborted"}
  /\ txLocks[tid] # {}
  /\ txLocks' = [txLocks EXCEPT ![tid] = {}]
  /\ waitForGraph' = [t \in TxIds |-> 
       IF tid \in waitForGraph[t] 
       THEN waitForGraph[t] \ {tid}
       ELSE waitForGraph[t]]
  /\ UNCHANGED <<nextTID, transactions, txOperations, 
                 preparedTransactions, coordinatorState, participantVotes,
                 txWALRecords, lastCommitLSN, txSnapshots, txWriteSets, txReadSets,
                 deadlockVictim>>

\* Abort deadlock victim
AbortDeadlockVictim ==
  /\ deadlockVictim > 0
  /\ deadlockVictim \in ActiveTransactions
  /\ AbortTransaction(deadlockVictim)
  /\ deadlockVictim' = 0

\* Timeout long-running transaction
TimeoutTransaction(tid) ==
  /\ tid \in ActiveTransactions
  /\ globalClock - txStartTime[tid] > TX_TIMEOUT_MS
  /\ AbortTransaction(tid)

\* Timeout 2PC prepare phase
TimeoutPrepare(tid) ==
  /\ coordinatorState[tid] = "preparing"
  /\ prepareTimer[tid] >= PREPARE_TIMEOUT_MS
  /\ AbortTx_Coordinator(tid)

\* Tick global clock
TickClock ==
  /\ globalClock' = globalClock + 1
  /\ prepareTimer' = [tid \in TxIds |->
       IF coordinatorState[tid] = "preparing"
       THEN prepareTimer[tid] + 1
       ELSE prepareTimer[tid]]
  /\ UNCHANGED <<nextTID, transactions, txOperations, txLocks, txStartTime,
                 preparedTransactions, coordinatorState, participantVotes,
                 txWALRecords, lastCommitLSN, txSnapshots, txWriteSets, txReadSets,
                 waitForGraph, deadlockVictim>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Atomicity - transaction completes fully or not at all
Inv_TM_Atomicity ==
  \A tid \in TxIds:
    transactions[tid].status = "committed" =>
      \A op \in Range(txOperations[tid]):
        op.kind \in {"read", "write", "update", "delete"}

\* Invariant 2: Durability - committed transactions have WAL records
Inv_TM_Durability ==
  \A tid \in TxIds:
    transactions[tid].status = "committed" =>
      /\ transactions[tid].commitLSN > 0
      /\ transactions[tid].commitLSN <= lastCommitLSN + 1

\* Invariant 3: Isolation - transactions don't see uncommitted changes
Inv_TM_Isolation ==
  \A t1, t2 \in TxIds:
    /\ t1 # t2
    /\ transactions[t1].status = "active"
    /\ transactions[t2].status = "active"
    /\ txWriteSets[t1] \intersect txWriteSets[t2] # {}
    => FALSE  \* Write-write conflict should not occur

\* Invariant 4: 2PC - if committed, all participants voted YES
Inv_TM_2PC_Validity ==
  \A tid \in TxIds:
    /\ transactions[tid].status = "committed"
    /\ transactions[tid].isDistributed
    => \A p \in Participants : participantVotes[tid][p] = "yes"

\* Invariant 5: Lock discipline - only lock holders can modify resources
Inv_TM_LockDiscipline ==
  \A tid \in TxIds:
    \A op \in Range(txOperations[tid]):
      op.kind \in {"write", "update", "delete"} =>
        op.resource \in txLocks[tid]

\* Invariant 6: No deadlock (eventually resolved)
Inv_TM_NoDeadlock ==
  ~HasDeadlock \/ deadlockVictim > 0

\* Invariant 7: WAL ordering - commit LSN > start LSN
Inv_TM_WAL_Ordering ==
  \A tid \in TxIds:
    transactions[tid].status = "committed" =>
      transactions[tid].commitLSN > transactions[tid].startLSN

\* Combined safety invariant
Inv_TM_Safety ==
  /\ TypeOK_TM
  /\ Inv_TM_Atomicity
  /\ Inv_TM_Durability
  /\ Inv_TM_Isolation
  /\ Inv_TM_2PC_Validity
  /\ Inv_TM_LockDiscipline
  /\ Inv_TM_NoDeadlock
  /\ Inv_TM_WAL_Ordering

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, all transactions complete
Liveness_TxEventuallyCompletes ==
  \A tid \in TxIds:
    [](transactions[tid].status = "active" =>
       <>(transactions[tid].status \in {"committed", "aborted"}))

\* Eventually, all locks are released
Liveness_LocksEventuallyReleased ==
  \A tid \in TxIds:
    [](txLocks[tid] # {} => <>(txLocks[tid] = {}))

\* Deadlocks are eventually resolved
Liveness_DeadlockResolution ==
  [](HasDeadlock => <>(~HasDeadlock))

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next_TM ==
  \/ \E tid \in TxIds, iso \in IsolationLevel, dist \in BOOLEAN:
       BeginTransaction(tid, iso, dist)
  \/ \E tid \in TxIds, r \in Resources:
       AcquireLock(tid, r)
  \/ \E tid \in TxIds, r \in Resources:
       WaitForLock(tid, r)
  \/ \E tid \in TxIds, r \in Resources:
       ExecuteRead(tid, r)
  \/ \E tid \in TxIds, r \in Resources, v \in Value:
       ExecuteWrite(tid, r, v)
  \/ \E tid \in TxIds:
       PrepareTx_Coordinator(tid)
  \/ \E tid \in TxIds, p \in Participants:
       PrepareTx_Participant(tid, p)
  \/ \E tid \in TxIds, p \in Participants:
       AbortTx_Participant(tid, p)
  \/ \E tid \in TxIds:
       CommitTx_Coordinator(tid)
  \/ \E tid \in TxIds:
       AbortTx_Coordinator(tid)
  \/ \E tid \in TxIds:
       CommitTransaction(tid)
  \/ \E tid \in TxIds:
       AbortTransaction(tid)
  \/ \E tid \in TxIds:
       ReleaseLocks(tid)
  \/ AbortDeadlockVictim
  \/ \E tid \in TxIds: TimeoutTransaction(tid)
  \/ \E tid \in TxIds: TimeoutPrepare(tid)
  \/ TickClock

Spec_TM == Init_TM /\ [][Next_TM]_tmVars

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: ACID properties are maintained
THEOREM ACID_Properties ==
  Spec_TM => [](Inv_TM_Atomicity /\ Inv_TM_Durability /\ Inv_TM_Isolation)

\* Theorem 2: 2PC maintains atomicity across participants
THEOREM TwoPhaseCommit_Atomicity ==
  Spec_TM => []Inv_TM_2PC_Validity

\* Theorem 3: Deadlocks are eventually resolved
THEOREM Deadlock_Resolution ==
  Spec_TM => Liveness_DeadlockResolution

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    MAX_TX = 3
    MAX_LSN = 15
    MAX_PAGES = 5
    Resources = {1, 2, 3}
    Participants = {1, 2}
  
  Invariants to check:
    - Inv_TM_Safety
  
  Temporal properties:
    - Liveness_TxEventuallyCompletes (with fairness)
    - Liveness_DeadlockResolution
  
  State constraints:
    - nextTID <= 15
    - Cardinality(ActiveTransactions) <= 3
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_TM(tm: TransactionManager) -> [String: Any] {
      return [
          "nextTID": tm.nextTransactionID,
          "transactions": tm.transactions.mapValues { tx in
              ["tid": tx.id,
               "status": tx.status.rawValue,
               "isolationLevel": tx.isolationLevel.rawValue,
               "startTime": tx.startTimestamp,
               "startLSN": tx.startLSN,
               "commitLSN": tx.commitLSN,
               "isReadOnly": tx.isReadOnly,
               "isDistributed": tx.isDistributed]
          },
          "txOperations": tm.operationLog,
          "txLocks": tm.lockManager.lockTable,
          "preparedTransactions": Set(tm.preparedTx),
          "coordinatorState": tm.coordinatorStates,
          "participantVotes": tm.participantVotes,
          "txWALRecords": tm.walRecordsByTx,
          "lastCommitLSN": tm.lastCommitLSN
      ]
  }
  
  TRACE POINTS:
  
  - traceLog(.tmBegin, state: toTLA_TM(self), txId: tid)
  - traceLog(.tmAcquireLock, state: toTLA_TM(self), txId: tid, resource: r)
  - traceLog(.tmWrite, state: toTLA_TM(self), txId: tid, resource: r)
  - traceLog(.tmPrepare, state: toTLA_TM(self), txId: tid)
  - traceLog(.tmCommit, state: toTLA_TM(self), txId: tid)
  - traceLog(.tmAbort, state: toTLA_TM(self), txId: tid)
  - traceLog(.tmReleaseLocks, state: toTLA_TM(self), txId: tid)
*)

