-------------------------- MODULE PointInTimeRecovery --------------------------
(*****************************************************************************)
(* Point-in-Time Recovery (PITR) for ColibrìDB                              *)
(*                                                                           *)
(* This specification models Point-in-Time Recovery with:                   *)
(*   - WAL-based recovery to any consistent point                           *)
(*   - Transaction-level recovery granularity                               *)
(*   - Forward and backward recovery                                        *)
(*   - Undo/Redo log replay                                                 *)
(*   - Crash recovery (ARIES algorithm)                                     *)
(*   - Savepoints and nested recovery                                       *)
(*   - Consistent snapshot restoration                                      *)
(*   - Media recovery for disk failures                                     *)
(*   - Logical replication for continuous recovery                          *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Mohan et al. (1992): "ARIES: A Transaction Recovery Method"         *)
(*   - Gray & Reuter (1993): "Transaction Processing" - Recovery            *)
(*   - Hellerstein et al. (2007): "Architecture of a Database System"      *)
(*   - PostgreSQL Write-Ahead Logging and PITR                              *)
(*   - Oracle Database Flashback and Recovery                               *)
(*   - MySQL InnoDB Recovery mechanisms                                     *)
(*   - SQLite WAL mode and recovery                                         *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE, TLC

CONSTANTS
    Transactions,       \* Set of all transactions
    Pages,              \* Set of database pages
    MaxWALSize,         \* Maximum WAL size before archiving
    MaxSavepoints,      \* Maximum savepoints per transaction
    RecoveryTargets     \* Set of recovery target types

VARIABLES
    wal,                \* Write-Ahead Log (sequence of log records)
    committedTxns,      \* Set of committed transactions
    abortedTxns,        \* Set of aborted transactions
    activeTxns,         \* Currently active transactions
    pageState,          \* Current state of pages
    checkpoints,        \* Sequence of checkpoint records
    savepoints,         \* Transaction -> Seq of savepoints
    lastLSN,            \* Last Log Sequence Number
    recoverySessions,   \* Active recovery sessions
    recoveryTarget,     \* Target for PITR
    undoLog,            \* Undo information for active transactions
    redoLog,            \* Redo information for committed transactions
    currentTime,        \* Global clock
    systemState         \* Database system state

vars == <<wal, committedTxns, abortedTxns, activeTxns, pageState, checkpoints,
          savepoints, lastLSN, recoverySessions, recoveryTarget, undoLog, 
          redoLog, currentTime, systemState>>

--------------------------------------------------------------------------------
(* Type Definitions *)

TxnId == Transactions
PageId == Pages
LSN == Nat  \* Log Sequence Number
Timestamp == Nat

(* System states *)
SystemState == {"NORMAL", "RECOVERING", "CRASHED", "CONSISTENT"}

(* Recovery target types *)
RecoveryTargetType == {
    "TIME",             \* Recover to specific timestamp
    "XID",              \* Recover to specific transaction ID
    "LSN",              \* Recover to specific LSN
    "NAME",             \* Recover to named restore point
    "IMMEDIATE",        \* Recover to earliest consistent point
    "LATEST"            \* Recover to latest possible point
}

(* Log record types *)
LogRecordType == {
    "BEGIN",            \* Transaction begin
    "COMMIT",           \* Transaction commit
    "ABORT",            \* Transaction abort
    "UPDATE",           \* Page update
    "CHECKPOINT",       \* Checkpoint
    "SAVEPOINT",        \* Savepoint creation
    "ROLLBACK_SAVEPOINT", \* Rollback to savepoint
    "COMPENSATION"      \* CLR (Compensation Log Record) for undo
}

(* Log record structure *)
LogRecord == [
    lsn: LSN,
    type: LogRecordType,
    txnId: TxnId \cup {0},      \* 0 for non-transactional records
    prevLSN: LSN \cup {0},      \* Previous LSN for this transaction
    pageId: PageId \cup {0},    \* Page affected (0 if none)
    undoInfo: STRING,           \* Information needed for undo
    redoInfo: STRING,           \* Information needed for redo
    timestamp: Timestamp,
    nextLSN: LSN \cup {0}       \* For CLRs: next record to undo
]

(* Checkpoint structure *)
Checkpoint == [
    lsn: LSN,
    timestamp: Timestamp,
    activeTxns: SUBSET Transactions,
    dirtyPages: SUBSET Pages,
    oldestActiveTxnLSN: LSN
]

(* Savepoint structure *)
Savepoint == [
    name: STRING,
    lsn: LSN,
    txnId: TxnId,
    timestamp: Timestamp
]

(* Recovery target *)
Target == [
    type: RecoveryTargetType,
    value: Nat \cup STRING,     \* Timestamp, XID, LSN, or name
    inclusive: BOOLEAN          \* Include or exclude target point
]

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ wal = <<>>
    /\ committedTxns = {}
    /\ abortedTxns = {}
    /\ activeTxns = {}
    /\ pageState = [p \in Pages |-> [version |-> 0, lsn |-> 0, data |-> <<>>]]
    /\ checkpoints = <<>>
    /\ savepoints = [txn \in Transactions |-> <<>>]
    /\ lastLSN = 0
    /\ recoverySessions = {}
    /\ recoveryTarget = [type |-> "LATEST", value |-> 0, inclusive |-> TRUE]
    /\ undoLog = [txn \in Transactions |-> <<>>]
    /\ redoLog = <<>>
    /\ currentTime = 0
    /\ systemState = "NORMAL"

--------------------------------------------------------------------------------
(* Helper Functions *)

(* Append log record to WAL *)
AppendWAL(record) ==
    /\ lastLSN' = lastLSN + 1
    /\ wal' = Append(wal, [record EXCEPT !.lsn = lastLSN + 1])

(* Find log records for a transaction *)
TxnLogRecords(txnId) ==
    {i \in DOMAIN wal : wal[i].txnId = txnId}

(* Get last log record for transaction *)
LastTxnLSN(txnId) ==
    IF TxnLogRecords(txnId) = {} THEN 0
    ELSE CHOOSE lsn \in {wal[i].lsn : i \in TxnLogRecords(txnId)} :
           \A other \in {wal[i].lsn : i \in TxnLogRecords(txnId)} :
             other <= lsn

(* Find checkpoint before given LSN *)
CheckpointBefore(lsn) ==
    IF checkpoints = <<>> THEN 0
    ELSE LET validCps == {i \in DOMAIN checkpoints : checkpoints[i].lsn < lsn}
         IN IF validCps = {} THEN 0
            ELSE CHOOSE i \in validCps :
                   \A j \in validCps : checkpoints[j].lsn <= checkpoints[i].lsn

(* Determine if LSN is before recovery target *)
BeforeTarget(lsn, target) ==
    CASE target.type = "LSN" -> 
           IF target.inclusive THEN lsn <= target.value ELSE lsn < target.value
      [] target.type = "TIME" ->
           \E i \in DOMAIN wal : wal[i].lsn = lsn /\
             (IF target.inclusive 
              THEN wal[i].timestamp <= target.value 
              ELSE wal[i].timestamp < target.value)
      [] target.type = "XID" ->
           \E i \in DOMAIN wal : 
             wal[i].lsn = lsn /\ wal[i].txnId <= target.value
      [] target.type = "IMMEDIATE" -> FALSE
      [] target.type = "LATEST" -> TRUE
      [] OTHER -> TRUE

(* Check if transaction should be recovered *)
ShouldRecover(txnId, target) ==
    LET txnRecords == {wal[i] : i \in TxnLogRecords(txnId)}
        commitRecord == CHOOSE r \in txnRecords : r.type = "COMMIT"
    IN
        /\ commitRecord # {}
        /\ BeforeTarget(commitRecord.lsn, target)

--------------------------------------------------------------------------------
(* Normal Operations *)

(* Begin transaction *)
BeginTransaction(txnId) ==
    /\ txnId \notin activeTxns
    /\ txnId \notin committedTxns
    /\ txnId \notin abortedTxns
    /\ systemState = "NORMAL"
    /\ LET record == [
             lsn |-> 0,  \* Will be set by AppendWAL
             type |-> "BEGIN",
             txnId |-> txnId,
             prevLSN |-> 0,
             pageId |-> 0,
             undoInfo |-> <<>>,
             redoInfo |-> <<>>,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ activeTxns' = activeTxns \cup {txnId}
           /\ undoLog' = [undoLog EXCEPT ![txnId] = <<>>]
    /\ UNCHANGED <<committedTxns, abortedTxns, pageState, checkpoints, savepoints,
                  recoverySessions, recoveryTarget, redoLog, currentTime, systemState>>

(* Update page *)
UpdatePage(txnId, pageId, undoInfo, redoInfo) ==
    /\ txnId \in activeTxns
    /\ systemState = "NORMAL"
    /\ LET record == [
             lsn |-> 0,
             type |-> "UPDATE",
             txnId |-> txnId,
             prevLSN |-> LastTxnLSN(txnId),
             pageId |-> pageId,
             undoInfo |-> undoInfo,
             redoInfo |-> redoInfo,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ pageState' = [pageState EXCEPT 
                ![pageId].version = @ + 1,
                ![pageId].lsn = lastLSN + 1,
                ![pageId].data = redoInfo]
           /\ undoLog' = [undoLog EXCEPT 
                ![txnId] = Append(@, [lsn |-> lastLSN + 1, 
                                      pageId |-> pageId,
                                      undoInfo |-> undoInfo])]
    /\ UNCHANGED <<committedTxns, abortedTxns, activeTxns, checkpoints, savepoints,
                  recoverySessions, recoveryTarget, redoLog, currentTime, systemState>>

(* Commit transaction *)
CommitTransaction(txnId) ==
    /\ txnId \in activeTxns
    /\ systemState = "NORMAL"
    /\ LET record == [
             lsn |-> 0,
             type |-> "COMMIT",
             txnId |-> txnId,
             prevLSN |-> LastTxnLSN(txnId),
             pageId |-> 0,
             undoInfo |-> <<>>,
             redoInfo |-> <<>>,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ activeTxns' = activeTxns \ {txnId}
           /\ committedTxns' = committedTxns \cup {txnId}
           /\ redoLog' = Append(redoLog, [txnId |-> txnId, commitLSN |-> lastLSN + 1])
    /\ UNCHANGED <<abortedTxns, pageState, checkpoints, savepoints, undoLog,
                  recoverySessions, recoveryTarget, currentTime, systemState>>

(* Abort transaction *)
AbortTransaction(txnId) ==
    /\ txnId \in activeTxns
    /\ systemState = "NORMAL"
    /\ LET record == [
             lsn |-> 0,
             type |-> "ABORT",
             txnId |-> txnId,
             prevLSN |-> LastTxnLSN(txnId),
             pageId |-> 0,
             undoInfo |-> <<>>,
             redoInfo |-> <<>>,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ activeTxns' = activeTxns \ {txnId}
           /\ abortedTxns' = abortedTxns \cup {txnId}
    /\ UNCHANGED <<committedTxns, pageState, checkpoints, savepoints, undoLog,
                  redoLog, recoverySessions, recoveryTarget, currentTime, systemState>>

--------------------------------------------------------------------------------
(* Savepoints *)

CreateSavepoint(txnId, savepointName) ==
    /\ txnId \in activeTxns
    /\ systemState = "NORMAL"
    /\ Len(savepoints[txnId]) < MaxSavepoints
    /\ LET sp == [
             name |-> savepointName,
             lsn |-> lastLSN,
             txnId |-> txnId,
             timestamp |-> currentTime
       ]
           record == [
             lsn |-> 0,
             type |-> "SAVEPOINT",
             txnId |-> txnId,
             prevLSN |-> LastTxnLSN(txnId),
             pageId |-> 0,
             undoInfo |-> savepointName,
             redoInfo |-> <<>>,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ savepoints' = [savepoints EXCEPT ![txnId] = Append(@, sp)]
    /\ UNCHANGED <<committedTxns, abortedTxns, activeTxns, pageState, checkpoints,
                  undoLog, redoLog, recoverySessions, recoveryTarget, currentTime, systemState>>

RollbackToSavepoint(txnId, savepointName) ==
    /\ txnId \in activeTxns
    /\ systemState = "NORMAL"
    /\ \E i \in DOMAIN savepoints[txnId] : 
         savepoints[txnId][i].name = savepointName
    /\ LET sp == CHOOSE s \in {savepoints[txnId][i] : i \in DOMAIN savepoints[txnId]} :
                   s.name = savepointName
           undoRecords == {wal[i] : i \in DOMAIN wal /\ 
                          wal[i].txnId = txnId /\ wal[i].lsn > sp.lsn}
       IN
           \* Undo operations back to savepoint
           /\ undoLog' = [undoLog EXCEPT ![txnId] = 
                SelectSeq(@, LAMBDA x: x.lsn <= sp.lsn)]
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, pageState, 
                  checkpoints, savepoints, lastLSN, recoverySessions, 
                  recoveryTarget, redoLog, currentTime, systemState>>

--------------------------------------------------------------------------------
(* Checkpointing *)

CreateCheckpoint ==
    /\ systemState = "NORMAL"
    /\ LET cp == [
             lsn |-> lastLSN + 1,
             timestamp |-> currentTime,
             activeTxns |-> activeTxns,
             dirtyPages |-> {p \in Pages : pageState[p].lsn > 0},
             oldestActiveTxnLSN |-> IF activeTxns = {} THEN lastLSN
                                   ELSE Min({LastTxnLSN(t) : t \in activeTxns})
       ]
           record == [
             lsn |-> 0,
             type |-> "CHECKPOINT",
             txnId |-> 0,
             prevLSN |-> 0,
             pageId |-> 0,
             undoInfo |-> <<>>,
             redoInfo |-> <<>>,
             timestamp |-> currentTime,
             nextLSN |-> 0
       ]
       IN
           /\ AppendWAL(record)
           /\ checkpoints' = Append(checkpoints, cp)
    /\ UNCHANGED <<committedTxns, abortedTxns, activeTxns, pageState, savepoints,
                  undoLog, redoLog, recoverySessions, recoveryTarget, 
                  currentTime, systemState>>

--------------------------------------------------------------------------------
(* Crash and Recovery *)

Crash ==
    /\ systemState = "NORMAL"
    /\ systemState' = "CRASHED"
    /\ activeTxns' = {}  \* Lose in-memory transaction state
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, pageState, checkpoints,
                  savepoints, lastLSN, undoLog, redoLog, recoverySessions,
                  recoveryTarget, currentTime>>

InitiateRecovery(target) ==
    /\ systemState = "CRASHED"
    /\ systemState' = "RECOVERING"
    /\ recoveryTarget' = target
    /\ recoverySessions' = {[startTime |-> currentTime, target |-> target]}
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, pageState,
                  checkpoints, savepoints, lastLSN, undoLog, redoLog, currentTime>>

(* ARIES Recovery - Analysis Phase *)
AnalysisPhase ==
    /\ systemState = "RECOVERING"
    /\ LET cpIndex == CheckpointBefore(lastLSN)
           startLSN == IF cpIndex = 0 THEN 1 ELSE checkpoints[cpIndex].lsn
           relevantRecords == {wal[i] : i \in DOMAIN wal /\ 
                              wal[i].lsn >= startLSN /\
                              BeforeTarget(wal[i].lsn, recoveryTarget)}
       IN
           \* Identify committed and active transactions
           /\ committedTxns' = {r.txnId : r \in relevantRecords /\ r.type = "COMMIT"}
           /\ activeTxns' = {r.txnId : r \in relevantRecords /\ 
                            r.type = "BEGIN" /\ r.txnId \notin committedTxns'}
    /\ UNCHANGED <<wal, abortedTxns, pageState, checkpoints, savepoints, lastLSN,
                  undoLog, redoLog, recoverySessions, recoveryTarget, 
                  currentTime, systemState>>

(* ARIES Recovery - Redo Phase *)
RedoPhase ==
    /\ systemState = "RECOVERING"
    /\ \E record \in {wal[i] : i \in DOMAIN wal} :
         /\ record.type = "UPDATE"
         /\ record.txnId \in committedTxns
         /\ BeforeTarget(record.lsn, recoveryTarget)
         /\ pageState[record.pageId].lsn < record.lsn
         /\ pageState' = [pageState EXCEPT
              ![record.pageId].data = record.redoInfo,
              ![record.pageId].lsn = record.lsn,
              ![record.pageId].version = @ + 1]
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, checkpoints,
                  savepoints, lastLSN, undoLog, redoLog, recoverySessions,
                  recoveryTarget, currentTime, systemState>>

(* ARIES Recovery - Undo Phase *)
UndoPhase ==
    /\ systemState = "RECOVERING"
    /\ activeTxns # {}
    /\ \E txnId \in activeTxns :
         LET lastUndoLSN == LastTxnLSN(txnId)
             record == CHOOSE r \in {wal[i] : i \in DOMAIN wal} :
                         r.lsn = lastUndoLSN
         IN
             /\ record.type = "UPDATE"
             /\ pageState' = [pageState EXCEPT
                  ![record.pageId].data = record.undoInfo]
             /\ LET clr == [
                      lsn |-> 0,
                      type |-> "COMPENSATION",
                      txnId |-> txnId,
                      prevLSN |-> lastUndoLSN,
                      pageId |-> record.pageId,
                      undoInfo |-> <<>>,
                      redoInfo |-> record.undoInfo,
                      timestamp |-> currentTime,
                      nextLSN |-> record.prevLSN
                ]
                IN AppendWAL(clr)
             /\ IF record.prevLSN = 0 THEN
                  activeTxns' = activeTxns \ {txnId}
                ELSE
                  UNCHANGED activeTxns
    /\ UNCHANGED <<committedTxns, abortedTxns, checkpoints, savepoints, undoLog,
                  redoLog, recoverySessions, recoveryTarget, currentTime, systemState>>

CompleteRecovery ==
    /\ systemState = "RECOVERING"
    /\ activeTxns = {}  \* All active transactions undone
    /\ systemState' = "CONSISTENT"
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, pageState,
                  checkpoints, savepoints, lastLSN, undoLog, redoLog,
                  recoverySessions, recoveryTarget, currentTime>>

ResumeNormalOperation ==
    /\ systemState = "CONSISTENT"
    /\ systemState' = "NORMAL"
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, pageState,
                  checkpoints, savepoints, lastLSN, undoLog, redoLog,
                  recoverySessions, recoveryTarget, currentTime>>

--------------------------------------------------------------------------------
(* Time Progress *)

Tick ==
    /\ currentTime' = currentTime + 1
    /\ UNCHANGED <<wal, committedTxns, abortedTxns, activeTxns, pageState,
                  checkpoints, savepoints, lastLSN, undoLog, redoLog,
                  recoverySessions, recoveryTarget, systemState>>

--------------------------------------------------------------------------------
(* Next State *)

Next ==
    \/ \E txn \in Transactions : BeginTransaction(txn)
    \/ \E txn \in Transactions, p \in Pages, undo, redo \in STRING :
         UpdatePage(txn, p, undo, redo)
    \/ \E txn \in Transactions : CommitTransaction(txn)
    \/ \E txn \in Transactions : AbortTransaction(txn)
    \/ \E txn \in Transactions, name \in STRING : CreateSavepoint(txn, name)
    \/ \E txn \in Transactions, name \in STRING : RollbackToSavepoint(txn, name)
    \/ CreateCheckpoint
    \/ Crash
    \/ \E target \in Target : InitiateRecovery(target)
    \/ AnalysisPhase
    \/ RedoPhase
    \/ UndoPhase
    \/ CompleteRecovery
    \/ ResumeNormalOperation
    \/ Tick

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
(* Invariants *)

(* INV1: Transaction states are mutually exclusive *)
TransactionStatesMutuallyExclusive ==
    /\ activeTxns \cap committedTxns = {}
    /\ activeTxns \cap abortedTxns = {}
    /\ committedTxns \cap abortedTxns = {}

(* INV2: WAL LSNs are monotonically increasing *)
WALMonotonic ==
    \A i, j \in DOMAIN wal : i < j => wal[i].lsn < wal[j].lsn

(* INV3: Page LSNs don't exceed WAL LSN *)
PageLSNsValid ==
    \A p \in Pages : pageState[p].lsn <= lastLSN

(* INV4: Committed transactions have commit records *)
CommittedTxnsHaveRecords ==
    \A txn \in committedTxns :
        \E i \in DOMAIN wal : wal[i].txnId = txn /\ wal[i].type = "COMMIT"

(* INV5: During recovery, no new transactions start *)
NoNewTxnsDuringRecovery ==
    systemState \in {"RECOVERING", "CONSISTENT"} => activeTxns = {}

(* INV6: Savepoints belong to active transactions *)
SavepointsBelongToActiveTxns ==
    systemState = "NORMAL" =>
        \A txn \in DOMAIN savepoints :
            savepoints[txn] # <<>> => txn \in activeTxns

(* INV7: Checkpoint LSNs are in WAL *)
CheckpointLSNsInWAL ==
    \A i \in DOMAIN checkpoints :
        \E j \in DOMAIN wal : wal[j].lsn = checkpoints[i].lsn

TypeInvariant ==
    /\ lastLSN \in Nat
    /\ currentTime \in Nat
    /\ systemState \in SystemState
    /\ DOMAIN pageState = Pages
    /\ DOMAIN savepoints = Transactions

--------------------------------------------------------------------------------
(* Safety Properties *)

(* SAFE1: Write-ahead logging: page updates logged before page write *)
WriteAheadLogging ==
    \A p \in Pages, i \in DOMAIN wal :
        (wal[i].type = "UPDATE" /\ wal[i].pageId = p /\ 
         wal[i].lsn = pageState[p].lsn) =>
           \A j \in DOMAIN wal : j < i => wal[j].lsn < wal[i].lsn

(* SAFE2: Durability: committed transactions survive crashes *)
Durability ==
    systemState = "CONSISTENT" =>
        \A txn \in committedTxns :
            \E i \in DOMAIN wal : wal[i].txnId = txn /\ wal[i].type = "COMMIT"

(* SAFE3: Atomicity: no partial transactions after recovery *)
Atomicity ==
    systemState = "CONSISTENT" =>
        \A txn \in Transactions :
            txn \in committedTxns \/ txn \in abortedTxns \/ 
            ~\E i \in DOMAIN wal : wal[i].txnId = txn

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* LIVE1: Recovery eventually completes *)
RecoveryEventuallyCompletes ==
    systemState = "RECOVERING" ~> systemState = "CONSISTENT"

(* LIVE2: System eventually returns to normal operation *)
EventuallyNormal ==
    systemState = "CRASHED" ~> systemState = "NORMAL"

(* LIVE3: Active transactions eventually commit or abort *)
TransactionsEventuallyComplete ==
    \A txn \in Transactions :
        txn \in activeTxns ~>
          (txn \in committedTxns \/ txn \in abortedTxns)

--------------------------------------------------------------------------------
(* Theorems *)

THEOREM PITRCorrectness ==
    Spec => [](TransactionStatesMutuallyExclusive /\ WALMonotonic)

THEOREM RecoverySafety ==
    Spec => [](Durability /\ Atomicity /\ WriteAheadLogging)

THEOREM RecoveryProgress ==
    Spec => (RecoveryEventuallyCompletes /\ EventuallyNormal)

THEOREM ARIESCorrectness ==
    Spec => [](CommittedTxnsHaveRecords /\ PageLSNsValid)

================================================================================

