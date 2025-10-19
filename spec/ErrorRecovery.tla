---------------------------- MODULE ErrorRecovery ----------------------------
(***************************************************************************
 * TLA+ Specification: Error Handling and Recovery
 *
 * Based on:
 * [1] Gray, J. (1981).
 *     "The Transaction Concept: Virtues and Limitations"
 *     Proceedings of VLDB, pp. 144-154.
 *     Transaction recovery principles
 *
 * [2] Gray, J., & Reuter, A. (1992).
 *     "Transaction Processing: Concepts and Techniques"
 *     Morgan Kaufmann. Chapter 10: Crash Recovery
 *     ISBN: 1558601902
 *     Comprehensive recovery theory
 *
 * [3] Mohan, C., & Narang, I. (1992).
 *     "Recovery and Coherency-Control Protocols for Fast Intersystem 
 *      Page Transfer and Fine-Granularity Locking in a Shared Disks 
 *      Transaction Environment"
 *     Proceedings of VLDB, pp. 193-207.
 *     Advanced recovery techniques
 *
 * [4] Avizienis, A., Laprie, J. C., Randell, B., & Landwehr, C. (2004).
 *     "Basic Concepts and Taxonomy of Dependable and Secure Computing"
 *     IEEE Transactions on Dependable and Secure Computing, 1(1), 11-33.
 *     DOI: 10.1109/TDSC.2004.2
 *     Error and failure classification
 *
 * This specification models error recovery including:
 * - Error detection and classification
 * - Error propagation and containment
 * - Recovery strategies (retry, rollback, compensation)
 * - Checkpoint-based recovery
 * - Transaction abort and rollback
 * - System-level recovery
 * - Fault tolerance
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxRetries,         \* Maximum retry attempts
    MaxCheckpoints,     \* Maximum checkpoints to keep
    Components,         \* System components
    ErrorTypes,         \* Types of errors
    RecoveryStrategies  \* Available recovery strategies

ASSUME MaxRetries \in Nat \ {0}
ASSUME MaxCheckpoints \in Nat \ {0}

(***************************************************************************
 * Error Classifications (Avizienis 2004, Section 3)
 ***************************************************************************)
\* ErrorTypes defined as constant, but typically includes:
\* - TRANSIENT: temporary error (retry may succeed)
\* - PERMANENT: persistent error (requires intervention)
\* - INTERMITTENT: sporadic error
\* - BYZANTINE: arbitrary/malicious error

(***************************************************************************
 * Component States (Gray 1992, Chapter 10)
 ***************************************************************************)
ComponentStates == {
    "OPERATIONAL",      \* Component working normally
    "ERROR_DETECTED",   \* Error detected, not yet handled
    "RECOVERING",       \* Recovery in progress
    "FAILED",           \* Component failed
    "RECOVERED"         \* Recovery completed
}

(***************************************************************************
 * Recovery Strategy Types (Gray 1992)
 ***************************************************************************)
\* RecoveryStrategies defined as constant, typically:
\* - RETRY: re-execute failed operation
\* - ROLLBACK: undo to consistent state
\* - CHECKPOINT_RESTORE: restore from checkpoint
\* - FAILOVER: switch to backup component
\* - COMPENSATE: execute compensating transaction

VARIABLES
    \* Component state
    componentStates,    \* [component |-> state]
    componentErrors,    \* [component |-> Set of errors]
    
    \* Error tracking
    errors,             \* [errorId |-> error_record]
    nextErrorId,        \* Next error ID
    errorLog,           \* Sequence of error events
    
    \* Recovery state
    recoveryActions,    \* [errorId |-> recovery_action]
    retryCounters,      \* [errorId |-> retry_count]
    recoveryInProgress, \* Set of error IDs being recovered
    
    \* Checkpoints (Gray 1992, Section 10.3)
    checkpoints,        \* [component |-> Sequence of checkpoints]
    lastCheckpointId,   \* [component |-> last_checkpoint_id]
    
    \* System state snapshots
    stateSnapshots,     \* [checkpointId |-> state_snapshot]
    
    \* Statistics
    totalErrors,        \* Total errors detected
    totalRecoveries,    \* Total successful recoveries
    totalFailures       \* Total recovery failures

componentVars == <<componentStates, componentErrors>>
errorVars == <<errors, nextErrorId, errorLog>>
recoveryVars == <<recoveryActions, retryCounters, recoveryInProgress>>
checkpointVars == <<checkpoints, lastCheckpointId, stateSnapshots>>
statsVars == <<totalErrors, totalRecoveries, totalFailures>>
vars == <<componentVars, errorVars, recoveryVars, checkpointVars, statsVars>>

(***************************************************************************
 * Error Record Structure
 ***************************************************************************)
ErrorRecord == [
    errorId: Nat,
    component: Components,
    errorType: ErrorTypes,
    timestamp: Nat,
    description: STRING,
    severity: {"LOW", "MEDIUM", "HIGH", "CRITICAL"},
    recoverable: BOOLEAN
]

(***************************************************************************
 * Recovery Action Structure
 ***************************************************************************)
RecoveryAction == [
    errorId: Nat,
    strategy: RecoveryStrategies,
    attempts: Nat,
    success: BOOLEAN
]

(***************************************************************************
 * Checkpoint Structure (Gray 1992)
 ***************************************************************************)
Checkpoint == [
    checkpointId: Nat,
    component: Components,
    timestamp: Nat,
    state: [STRING -> Value]
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ componentStates \in [Components -> ComponentStates]
    /\ componentErrors \in [Components -> SUBSET Nat]
    /\ errors \in [Nat -> ErrorRecord]
    /\ nextErrorId \in Nat
    /\ errorLog \in Seq(ErrorRecord)
    /\ recoveryActions \in [Nat -> RecoveryAction]
    /\ retryCounters \in [Nat -> 0..MaxRetries]
    /\ recoveryInProgress \subseteq Nat
    /\ checkpoints \in [Components -> Seq(Checkpoint)]
    /\ lastCheckpointId \in [Components -> Nat]
    /\ stateSnapshots \in [Nat -> [STRING -> Value]]
    /\ totalErrors \in Nat
    /\ totalRecoveries \in Nat
    /\ totalFailures \in Nat

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ componentStates = [c \in Components |-> "OPERATIONAL"]
    /\ componentErrors = [c \in Components |-> {}]
    /\ errors = [e \in {} |-> {}]
    /\ nextErrorId = 1
    /\ errorLog = <<>>
    /\ recoveryActions = [e \in {} |-> {}]
    /\ retryCounters = [e \in {} |-> 0]
    /\ recoveryInProgress = {}
    /\ checkpoints = [c \in Components |-> <<>>]
    /\ lastCheckpointId = [c \in Components |-> 0]
    /\ stateSnapshots = [s \in {} |-> [x \in {} |-> NULL]]
    /\ totalErrors = 0
    /\ totalRecoveries = 0
    /\ totalFailures = 0

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Check if error is recoverable
IsRecoverable(errorId) ==
    errorId \in DOMAIN errors /\ errors[errorId].recoverable

\* Check if retry limit reached
RetryLimitReached(errorId) ==
    errorId \in DOMAIN retryCounters /\ 
    retryCounters[errorId] >= MaxRetries

\* Get latest checkpoint for component
LatestCheckpoint(component) ==
    IF lastCheckpointId[component] = 0
    THEN NULL
    ELSE LET chkpts == checkpoints[component]
         IN chkpts[Len(chkpts)]

(***************************************************************************
 * Actions: Error Detection (Avizienis 2004)
 ***************************************************************************)

\* Detect and report error
DetectError(component, errorType, severity, recoverable) ==
    /\ component \in Components
    /\ errorType \in ErrorTypes
    /\ severity \in {"LOW", "MEDIUM", "HIGH", "CRITICAL"}
    /\ componentStates[component] = "OPERATIONAL"
    /\ LET errorId == nextErrorId
           error == [
               errorId |-> errorId,
               component |-> component,
               errorType |-> errorType,
               timestamp |-> totalErrors,
               description |-> "Error detected",
               severity |-> severity,
               recoverable |-> recoverable
           ]
       IN
        /\ errors' = errors @@ (errorId :> error)
        /\ nextErrorId' = nextErrorId + 1
        /\ errorLog' = Append(errorLog, error)
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "ERROR_DETECTED"]
        /\ componentErrors' = [componentErrors EXCEPT 
            ![component] = @ \cup {errorId}]
        /\ totalErrors' = totalErrors + 1
        /\ UNCHANGED <<recoveryVars, checkpointVars, totalRecoveries, 
                       totalFailures>>

(***************************************************************************
 * Actions: Checkpoint Management (Gray 1992, Section 10.3)
 ***************************************************************************)

\* Create checkpoint for component
CreateCheckpoint(component, state) ==
    /\ component \in Components
    /\ componentStates[component] = "OPERATIONAL"
    /\ Len(checkpoints[component]) < MaxCheckpoints
    /\ LET checkpointId == lastCheckpointId[component] + 1
           chkpt == [
               checkpointId |-> checkpointId,
               component |-> component,
               timestamp |-> totalErrors,
               state |-> state
           ]
       IN
        /\ checkpoints' = [checkpoints EXCEPT 
            ![component] = Append(@, chkpt)]
        /\ lastCheckpointId' = [lastCheckpointId EXCEPT 
            ![component] = checkpointId]
        /\ stateSnapshots' = stateSnapshots @@ (checkpointId :> state)
        /\ UNCHANGED <<componentVars, errorVars, recoveryVars, statsVars>>

\* Remove old checkpoints (garbage collection)
PruneCheckpoints(component) ==
    /\ component \in Components
    /\ Len(checkpoints[component]) > MaxCheckpoints
    /\ LET chkpts == checkpoints[component]
           pruned == SubSeq(chkpts, 2, Len(chkpts))
       IN
        /\ checkpoints' = [checkpoints EXCEPT ![component] = pruned]
        /\ UNCHANGED <<componentVars, errorVars, recoveryVars, 
                       lastCheckpointId, stateSnapshots, statsVars>>

(***************************************************************************
 * Actions: Recovery Strategies (Gray 1992, Chapter 10)
 ***************************************************************************)

\* Retry failed operation (for transient errors)
RetryOperation(errorId) ==
    /\ errorId \in DOMAIN errors
    /\ errors[errorId].errorType = "TRANSIENT"
    /\ IsRecoverable(errorId)
    /\ ~RetryLimitReached(errorId)
    /\ errorId \notin recoveryInProgress
    /\ LET component == errors[errorId].component
       IN
        /\ recoveryInProgress' = recoveryInProgress \cup {errorId}
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "RECOVERING"]
        /\ retryCounters' = [retryCounters EXCEPT ![errorId] = @ + 1]
        /\ UNCHANGED <<componentErrors, errorVars, recoveryActions, 
                       checkpointVars, statsVars>>

\* Complete successful retry
RetrySuccess(errorId) ==
    /\ errorId \in recoveryInProgress
    /\ LET component == errors[errorId].component
       IN
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "RECOVERED"]
        /\ componentErrors' = [componentErrors EXCEPT 
            ![component] = @ \ {errorId}]
        /\ recoveryInProgress' = recoveryInProgress \ {errorId}
        /\ totalRecoveries' = totalRecoveries + 1
        /\ UNCHANGED <<errorVars, recoveryActions, retryCounters, 
                       checkpointVars, totalErrors, totalFailures>>

\* Retry failed (exhaust retries)
RetryFailed(errorId) ==
    /\ errorId \in recoveryInProgress
    /\ RetryLimitReached(errorId)
    /\ LET component == errors[errorId].component
       IN
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "FAILED"]
        /\ recoveryInProgress' = recoveryInProgress \ {errorId}
        /\ totalFailures' = totalFailures + 1
        /\ UNCHANGED <<componentErrors, errorVars, recoveryActions, 
                       retryCounters, checkpointVars, totalErrors, 
                       totalRecoveries>>

\* Rollback using checkpoint
RollbackToCheckpoint(component, errorId) ==
    /\ component \in Components
    /\ errorId \in DOMAIN errors
    /\ errors[errorId].component = component
    /\ IsRecoverable(errorId)
    /\ LET chkpt == LatestCheckpoint(component)
       IN
        /\ chkpt # NULL
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "RECOVERING"]
        /\ recoveryInProgress' = recoveryInProgress \cup {errorId}
        /\ recoveryActions' = recoveryActions @@ (errorId :> [
            errorId |-> errorId,
            strategy |-> "CHECKPOINT_RESTORE",
            attempts |-> 1,
            success |-> TRUE
           ])
        /\ UNCHANGED <<componentErrors, errorVars, retryCounters, 
                       checkpointVars, statsVars>>

\* Complete checkpoint restore
CompleteCheckpointRestore(component, errorId) ==
    /\ component \in Components
    /\ errorId \in recoveryInProgress
    /\ errors[errorId].component = component
    /\ LET action == recoveryActions[errorId]
       IN
        /\ action.strategy = "CHECKPOINT_RESTORE"
        /\ componentStates' = [componentStates EXCEPT 
            ![component] = "RECOVERED"]
        /\ componentErrors' = [componentErrors EXCEPT 
            ![component] = @ \ {errorId}]
        /\ recoveryInProgress' = recoveryInProgress \ {errorId}
        /\ totalRecoveries' = totalRecoveries + 1
        /\ UNCHANGED <<errorVars, recoveryActions, retryCounters, 
                       checkpointVars, totalErrors, totalFailures>>

\* Compensating action (for irreversible operations)
ExecuteCompensatingAction(component, errorId) ==
    /\ component \in Components
    /\ errorId \in DOMAIN errors
    /\ errors[errorId].component = component
    /\ IsRecoverable(errorId)
    /\ componentStates' = [componentStates EXCEPT 
        ![component] = "RECOVERING"]
    /\ recoveryInProgress' = recoveryInProgress \cup {errorId}
    /\ recoveryActions' = recoveryActions @@ (errorId :> [
        errorId |-> errorId,
        strategy |-> "COMPENSATE",
        attempts |-> 1,
        success |-> TRUE
       ])
    /\ totalRecoveries' = totalRecoveries + 1
    /\ UNCHANGED <<componentErrors, errorVars, retryCounters, 
                   checkpointVars, totalErrors, totalFailures>>

(***************************************************************************
 * Actions: Recovery Completion
 ***************************************************************************)

\* Mark component as recovered
MarkComponentRecovered(component) ==
    /\ component \in Components
    /\ componentStates[component] = "RECOVERING"
    /\ componentErrors[component] = {}
    /\ componentStates' = [componentStates EXCEPT 
        ![component] = "OPERATIONAL"]
    /\ UNCHANGED <<componentErrors, errorVars, recoveryVars, 
                   checkpointVars, statsVars>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E c \in Components, et \in ErrorTypes, s \in {"LOW", "MEDIUM", "HIGH", "CRITICAL"},
          r \in BOOLEAN :
        DetectError(c, et, s, r)
    \/ \E c \in Components, state \in [STRING -> Value] :
        CreateCheckpoint(c, state)
    \/ \E c \in Components : PruneCheckpoints(c)
    \/ \E e \in DOMAIN errors : RetryOperation(e)
    \/ \E e \in recoveryInProgress : RetrySuccess(e)
    \/ \E e \in recoveryInProgress : RetryFailed(e)
    \/ \E c \in Components, e \in DOMAIN errors :
        RollbackToCheckpoint(c, e)
    \/ \E c \in Components, e \in recoveryInProgress :
        CompleteCheckpointRestore(c, e)
    \/ \E c \in Components, e \in DOMAIN errors :
        ExecuteCompensatingAction(c, e)
    \/ \E c \in Components : MarkComponentRecovered(c)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Gray 1992)
 ***************************************************************************)

\* No component remains in error state indefinitely
ErrorsEventuallyHandled ==
    \A c \in Components :
        componentStates[c] = "ERROR_DETECTED" =>
            <>(componentStates[c] \in {"RECOVERING", "RECOVERED", "FAILED"})

\* Recovery attempts bounded
RecoveryAttemptsBounded ==
    \A e \in DOMAIN retryCounters :
        retryCounters[e] <= MaxRetries

\* Checkpoint limit respected
CheckpointLimitRespected ==
    \A c \in Components :
        Len(checkpoints[c]) <= MaxCheckpoints

\* No inconsistent recovery states
NoInconsistentRecovery ==
    \A c \in Components :
        componentStates[c] = "RECOVERED" => componentErrors[c] = {}

Safety ==
    /\ RecoveryAttemptsBounded
    /\ CheckpointLimitRespected
    /\ NoInconsistentRecovery

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Recoverable errors eventually recovered
RecoverableErrorsEventuallyRecovered ==
    \A e \in DOMAIN errors :
        IsRecoverable(e) ~> 
            (e \notin recoveryInProgress /\ 
             errors[e].component \in 
                {c \in Components : componentStates[c] = "RECOVERED"})

\* Components eventually return to operational state
ComponentsEventuallyOperational ==
    \A c \in Components :
        componentStates[c] = "ERROR_DETECTED" ~>
            <>(componentStates[c] = "OPERATIONAL")

Liveness ==
    /\ ErrorsEventuallyHandled
    /\ RecoverableErrorsEventuallyRecovered

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []RecoveryAttemptsBounded

================================================================================

