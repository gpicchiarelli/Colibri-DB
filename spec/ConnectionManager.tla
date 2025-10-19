---------------------------- MODULE ConnectionManager ----------------------------
(***************************************************************************
 * TLA+ Specification: Connection Manager for Database Server
 *
 * Based on:
 * [1] Hellerstein, J. M., Stonebraker, M., & Hamilton, J. (2007).
 *     "Architecture of a Database System"
 *     Foundations and Trends in Databases, 1(2), 141-259.
 *     Section 2.1: Process Models
 *
 * [2] Stonebraker, M. (1981).
 *     "Operating System Support for Database Management"
 *     Communications of the ACM, 24(7), 412-418.
 *     Process structure models
 *
 * [3] Ahmad, M., Duan, S., Gavrilovska, A., & Pande, S. (2009).
 *     "Efficiently Adapting to Sharing Patterns in Thread Pool-Based Servers"
 *     IEEE IPDPS 2009.
 *     Thread pool management
 *
 * This specification models connection management including:
 * - Connection lifecycle (accept, authenticate, execute, close)
 * - Connection pooling with bounded resources
 * - Thread-per-connection and thread-pool models
 * - Session state management
 * - Resource limits and admission control
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxConnections,     \* Maximum concurrent connections
    MaxThreads,         \* Maximum worker threads
    MaxSessionTimeout,  \* Maximum idle timeout
    MaxQueueSize,       \* Maximum pending connection queue
    ClientIds           \* Set of potential client IDs

ASSUME MaxConnections \in Nat \ {0}
ASSUME MaxThreads \in Nat \ {0}
ASSUME MaxSessionTimeout \in Nat \ {0}
ASSUME MaxQueueSize \in Nat \ {0}

(***************************************************************************
 * Connection States (per Hellerstein Section 2.1.1)
 ***************************************************************************)
ConnectionStates == {
    "PENDING",       \* Accepted, waiting for authentication
    "AUTHENTICATING",\* Authentication in progress
    "AUTHENTICATED", \* Authenticated, ready to serve
    "ACTIVE",        \* Actively executing query
    "IDLE",          \* Connection open but idle
    "CLOSING",       \* Graceful shutdown initiated
    "CLOSED"         \* Connection terminated
}

(***************************************************************************
 * Process Models (per Stonebraker 1981)
 ***************************************************************************)
ProcessModels == {
    "PROCESS_PER_CONNECTION",  \* Fork process per connection (classic)
    "THREAD_PER_CONNECTION",   \* Thread per connection (modern)
    "THREAD_POOL"              \* Thread pool with work queue (scalable)
}

VARIABLES
    \* Connection state
    connections,        \* [cid |-> connection_record]
    connectionQueue,    \* Sequence of pending connection IDs
    nextConnId,         \* Next connection ID to assign
    
    \* Thread pool state
    threads,            \* [tid |-> thread_record]
    threadPool,         \* Set of available thread IDs
    busyThreads,        \* Set of busy thread IDs
    
    \* Session state
    sessions,           \* [cid |-> session_record]
    
    \* Resource tracking
    activeCount,        \* Number of active connections
    totalAccepted,      \* Total connections accepted
    totalRejected,      \* Total connections rejected
    
    \* Process model
    processModel        \* Current process model in use

connVars == <<connections, connectionQueue, nextConnId>>
threadVars == <<threads, threadPool, busyThreads>>
sessionVars == <<sessions>>
statsVars == <<activeCount, totalAccepted, totalRejected>>
vars == <<connVars, threadVars, sessionVars, statsVars, processModel>>

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ connections \in [Nat -> [
        cid: Nat,
        client: ClientIds,
        state: ConnectionStates,
        thread: Nat \cup {0},
        lastActivity: Nat,
        authenticated: BOOLEAN,
        sessionId: Nat \cup {0}
       ]]
    /\ connectionQueue \in Seq(Nat)
    /\ nextConnId \in Nat
    /\ threads \in [Nat -> [
        tid: Nat,
        busy: BOOLEAN,
        connection: Nat \cup {0}
       ]]
    /\ threadPool \subseteq (1..MaxThreads)
    /\ busyThreads \subseteq (1..MaxThreads)
    /\ sessions \in [Nat -> [
        sid: Nat,
        connection: Nat,
        txnId: Nat \cup {0},
        variables: [STRING -> Value]
       ]]
    /\ activeCount \in Nat
    /\ totalAccepted \in Nat
    /\ totalRejected \in Nat
    /\ processModel \in ProcessModels

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ connections = [x \in {} |-> {}]
    /\ connectionQueue = <<>>
    /\ nextConnId = 1
    /\ threads = [tid \in 1..MaxThreads |-> [
        tid |-> tid,
        busy |-> FALSE,
        connection |-> 0
       ]]
    /\ threadPool = 1..MaxThreads
    /\ busyThreads = {}
    /\ sessions = [x \in {} |-> {}]
    /\ activeCount = 0
    /\ totalAccepted = 0
    /\ totalRejected = 0
    /\ processModel \in ProcessModels

(***************************************************************************
 * Helper Functions
 ***************************************************************************)
\* Check if connection limit reached
ConnectionLimitReached ==
    activeCount >= MaxConnections

\* Check if queue is full
QueueFull ==
    Len(connectionQueue) >= MaxQueueSize

\* Get available thread
AvailableThread ==
    IF threadPool = {} 
    THEN 0
    ELSE CHOOSE tid \in threadPool : TRUE

\* Check if thread available
HasAvailableThread ==
    threadPool # {}

(***************************************************************************
 * Actions: Connection Lifecycle
 ***************************************************************************)

\* Accept new connection (Hellerstein Section 2.1.2)
AcceptConnection(client) ==
    /\ client \in ClientIds
    /\ ~ConnectionLimitReached
    /\ ~QueueFull
    /\ LET cid == nextConnId
           conn == [
               cid |-> cid,
               client |-> client,
               state |-> "PENDING",
               thread |-> 0,
               lastActivity |-> 0,
               authenticated |-> FALSE,
               sessionId |-> 0
           ]
       IN
        /\ connections' = connections @@ (cid :> conn)
        /\ connectionQueue' = Append(connectionQueue, cid)
        /\ nextConnId' = nextConnId + 1
        /\ activeCount' = activeCount + 1
        /\ totalAccepted' = totalAccepted + 1
        /\ UNCHANGED <<threads, threadPool, busyThreads, sessions, 
                       totalRejected, processModel>>

\* Reject connection due to resource limits
RejectConnection(client) ==
    /\ client \in ClientIds
    /\ ConnectionLimitReached \/ QueueFull
    /\ totalRejected' = totalRejected + 1
    /\ UNCHANGED <<connVars, threadVars, sessionVars, 
                   activeCount, totalAccepted, processModel>>

\* Assign thread to connection (Thread Pool Model)
AssignThreadToConnection ==
    /\ processModel = "THREAD_POOL"
    /\ connectionQueue # <<>>
    /\ HasAvailableThread
    /\ LET cid == Head(connectionQueue)
           tid == AvailableThread
           conn == connections[cid]
       IN
        /\ connections' = [connections EXCEPT 
            ![cid].state = "AUTHENTICATING",
            ![cid].thread = tid
           ]
        /\ connectionQueue' = Tail(connectionQueue)
        /\ threads' = [threads EXCEPT 
            ![tid].busy = TRUE,
            ![tid].connection = cid
           ]
        /\ threadPool' = threadPool \ {tid}
        /\ busyThreads' = busyThreads \cup {tid}
        /\ UNCHANGED <<nextConnId, sessionVars, statsVars, processModel>>

\* Authenticate connection
AuthenticateConnection(cid, success) ==
    /\ cid \in DOMAIN connections
    /\ connections[cid].state = "AUTHENTICATING"
    /\ LET conn == connections[cid]
       IN
        IF success
        THEN
            /\ LET sid == cid  \* Simple: use cid as session id
                   session == [
                       sid |-> sid,
                       connection |-> cid,
                       txnId |-> 0,
                       variables |-> [x \in {} |-> {}]
                   ]
               IN
                /\ connections' = [connections EXCEPT 
                    ![cid].state = "AUTHENTICATED",
                    ![cid].authenticated = TRUE,
                    ![cid].sessionId = sid
                   ]
                /\ sessions' = sessions @@ (sid :> session)
                /\ UNCHANGED <<connectionQueue, nextConnId, threadVars, 
                               statsVars, processModel>>
        ELSE
            \* Authentication failed - close connection
            /\ connections' = [connections EXCEPT ![cid].state = "CLOSING"]
            /\ UNCHANGED <<connectionQueue, nextConnId, threadVars, 
                           sessions, statsVars, processModel>>

\* Transition to active (executing query)
BeginExecution(cid) ==
    /\ cid \in DOMAIN connections
    /\ connections[cid].state \in {"AUTHENTICATED", "IDLE"}
    /\ connections[cid].authenticated = TRUE
    /\ connections' = [connections EXCEPT ![cid].state = "ACTIVE"]
    /\ UNCHANGED <<connectionQueue, nextConnId, threadVars, 
                   sessionVars, statsVars, processModel>>

\* Transition to idle (query completed)
EndExecution(cid) ==
    /\ cid \in DOMAIN connections
    /\ connections[cid].state = "ACTIVE"
    /\ connections' = [connections EXCEPT ![cid].state = "IDLE"]
    /\ UNCHANGED <<connectionQueue, nextConnId, threadVars, 
                   sessionVars, statsVars, processModel>>

\* Close connection gracefully
CloseConnection(cid) ==
    /\ cid \in DOMAIN connections
    /\ connections[cid].state \in {"IDLE", "AUTHENTICATED", "CLOSING"}
    /\ LET conn == connections[cid]
           tid == conn.thread
           sid == conn.sessionId
       IN
        /\ connections' = [x \in (DOMAIN connections) \ {cid} |-> 
                           IF x = cid THEN {} ELSE connections[x]]
        /\ IF tid \in busyThreads /\ processModel = "THREAD_POOL"
           THEN /\ threads' = [threads EXCEPT 
                    ![tid].busy = FALSE,
                    ![tid].connection = 0
                  ]
                /\ threadPool' = threadPool \cup {tid}
                /\ busyThreads' = busyThreads \ {tid}
           ELSE /\ UNCHANGED <<threads, threadPool, busyThreads>>
        /\ IF sid \in DOMAIN sessions
           THEN sessions' = [x \in (DOMAIN sessions) \ {sid} |-> 
                            IF x = sid THEN {} ELSE sessions[x]]
           ELSE UNCHANGED sessions
        /\ activeCount' = activeCount - 1
        /\ UNCHANGED <<connectionQueue, nextConnId, totalAccepted, 
                       totalRejected, processModel>>

\* Timeout idle connection
TimeoutConnection(cid) ==
    /\ cid \in DOMAIN connections
    /\ connections[cid].state = "IDLE"
    /\ connections[cid].lastActivity > MaxSessionTimeout
    /\ CloseConnection(cid)

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E client \in ClientIds : AcceptConnection(client)
    \/ \E client \in ClientIds : RejectConnection(client)
    \/ AssignThreadToConnection
    \/ \E cid \in DOMAIN connections, success \in BOOLEAN :
        AuthenticateConnection(cid, success)
    \/ \E cid \in DOMAIN connections : BeginExecution(cid)
    \/ \E cid \in DOMAIN connections : EndExecution(cid)
    \/ \E cid \in DOMAIN connections : CloseConnection(cid)
    \/ \E cid \in DOMAIN connections : TimeoutConnection(cid)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Hellerstein Section 2.1.3)
 ***************************************************************************)

\* Never exceed maximum connections
ConnectionLimitNotExceeded ==
    activeCount <= MaxConnections

\* Thread pool consistency
ThreadPoolConsistent ==
    /\ threadPool \cap busyThreads = {}
    /\ threadPool \cup busyThreads = 1..MaxThreads

\* Authenticated connections have sessions
AuthenticatedHaveSession ==
    \A cid \in DOMAIN connections :
        connections[cid].authenticated => connections[cid].sessionId \in DOMAIN sessions

\* Active connections have thread assigned (for thread pool model)
ActiveHaveThread ==
    \A cid \in DOMAIN connections :
        (processModel = "THREAD_POOL" /\ connections[cid].state = "ACTIVE")
            => connections[cid].thread \in busyThreads

\* Busy threads are assigned to connections
BusyThreadsAssigned ==
    \A tid \in busyThreads :
        threads[tid].connection \in DOMAIN connections

\* Session belongs to connection
SessionBelongsToConnection ==
    \A sid \in DOMAIN sessions :
        sessions[sid].connection \in DOMAIN connections

Safety ==
    /\ ConnectionLimitNotExceeded
    /\ ThreadPoolConsistent
    /\ AuthenticatedHaveSession
    /\ ActiveHaveThread
    /\ BusyThreadsAssigned
    /\ SessionBelongsToConnection

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Pending connections eventually processed
PendingEventuallyProcessed ==
    \A cid \in DOMAIN connections :
        connections[cid].state = "PENDING" 
            ~> connections[cid].state \in {"AUTHENTICATING", "CLOSING"}

\* Threads eventually become available
ThreadsEventuallyAvailable ==
    (processModel = "THREAD_POOL") => <>(threadPool # {})

\* Connections eventually close
ConnectionsEventuallyClose ==
    \A cid \in DOMAIN connections :
        <>(cid \notin DOMAIN connections)

Liveness ==
    /\ PendingEventuallyProcessed
    /\ ThreadsEventuallyAvailable
    /\ ConnectionsEventuallyClose

(***************************************************************************
 * Fairness
 ***************************************************************************)
Fairness ==
    /\ WF_vars(AssignThreadToConnection)
    /\ \A cid \in DOMAIN connections : WF_vars(CloseConnection(cid))
    /\ \A cid \in DOMAIN connections : WF_vars(TimeoutConnection(cid))

FairSpec == Spec /\ Fairness

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM FairSpec => Liveness

================================================================================

