---------------------------- MODULE Server ----------------------------
(***************************************************************************
 * TLA+ Specification: Database Server Architecture
 *
 * Based on:
 * [1] Hellerstein, J. M., Stonebraker, M., & Hamilton, J. (2007).
 *     "Architecture of a Database System"
 *     Foundations and Trends in Databases, 1(2), 141-259.
 *     Complete server architecture
 *
 * [2] Bernstein, P. A., Hadzilacos, V., & Goodman, N. (1987).
 *     "Concurrency Control and Recovery in Database Systems"
 *     Addison-Wesley. Chapter 7: System Architecture
 *     ISBN: 0201107155
 *
 * [3] Ramakrishnan, R., & Gehrke, J. (2003).
 *     "Database Management Systems" (3rd ed.)
 *     McGraw-Hill. Chapter 23: Parallel and Distributed Databases
 *     ISBN: 0072465638
 *
 * This specification models the complete database server including:
 * - Connection management
 * - Request processing pipeline
 * - Query execution
 * - Transaction coordination
 * - Resource management
 * - Error handling
 * - Admission control
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxConcurrentQueries,   \* Maximum concurrent query executions
    MaxConnectionsPerServer,\* Maximum connections per server
    MaxMemoryPerQuery,      \* Maximum memory per query (MB)
    TotalServerMemory,      \* Total server memory (MB)
    ServerIds,              \* Set of server IDs
    QueryTypes              \* Types of queries (SELECT, INSERT, etc.)

ASSUME MaxConcurrentQueries \in Nat \ {0}
ASSUME MaxConnectionsPerServer \in Nat \ {0}
ASSUME MaxMemoryPerQuery \in Nat \ {0}
ASSUME TotalServerMemory \in Nat \ {0}
ASSUME MaxMemoryPerQuery * MaxConcurrentQueries <= TotalServerMemory

(***************************************************************************
 * Server States (per Hellerstein Section 1)
 ***************************************************************************)
ServerStates == {
    "STARTING",      \* Server initializing
    "RUNNING",       \* Server operational
    "RECOVERY",      \* Server recovering from crash
    "MAINTENANCE",   \* Server in maintenance mode
    "SHUTTING_DOWN", \* Server shutting down gracefully
    "STOPPED"        \* Server stopped
}

(***************************************************************************
 * Query States (per Hellerstein Section 4)
 ***************************************************************************)
QueryStates == {
    "QUEUED",        \* Waiting for resources
    "PARSING",       \* Parsing SQL
    "PLANNING",      \* Query optimization
    "EXECUTING",     \* Executing query plan
    "COMPLETED",     \* Execution completed
    "FAILED",        \* Execution failed
    "CANCELLED"      \* Query cancelled
}

(***************************************************************************
 * Connection States
 ***************************************************************************)
ConnectionStates == {
    "ACTIVE",        \* Connection active
    "IDLE",          \* Connection idle
    "IN_TRANSACTION",\* Connection in transaction
    "CLOSED"         \* Connection closed
}

VARIABLES
    \* Server state
    serverState,         \* [sid |-> server_state]
    serverUptime,        \* [sid |-> uptime_seconds]
    
    \* Connection management
    connections,         \* [<<sid, cid>> |-> connection_record]
    connectionCount,     \* [sid |-> num_connections]
    
    \* Query execution
    queries,             \* [<<sid, qid>> |-> query_record]
    queryQueue,          \* [sid |-> Sequence of qid]
    activeQueries,       \* [sid |-> Set of qid]
    nextQueryId,         \* [sid |-> next_query_id]
    
    \* Resource management
    memoryAllocated,     \* [sid |-> allocated_memory_MB]
    cpuUtilization,      \* [sid |-> cpu_percent]
    diskIOPending,       \* [sid |-> pending_io_ops]
    
    \* Transaction coordination
    activeTxns,          \* [sid |-> Set of txn_id]
    preparedTxns,        \* [sid |-> Set of txn_id]
    
    \* Statistics
    totalQueriesProcessed, \* [sid |-> count]
    totalConnections,      \* [sid |-> count]
    totalErrors            \* [sid |-> count]

serverVars == <<serverState, serverUptime>>
connVars == <<connections, connectionCount>>
queryVars == <<queries, queryQueue, activeQueries, nextQueryId>>
resourceVars == <<memoryAllocated, cpuUtilization, diskIOPending>>
txnVars == <<activeTxns, preparedTxns>>
statsVars == <<totalQueriesProcessed, totalConnections, totalErrors>>
vars == <<serverVars, connVars, queryVars, resourceVars, txnVars, statsVars>>

(***************************************************************************
 * Connection Record Structure
 ***************************************************************************)
ConnectionRecord == [
    cid: Nat,
    state: ConnectionStates,
    txnId: Nat \cup {0},
    startTime: Nat,
    lastActivity: Nat,
    authenticated: BOOLEAN
]

(***************************************************************************
 * Query Record Structure
 ***************************************************************************)
QueryRecord == [
    qid: Nat,
    cid: Nat,
    type: QueryTypes,
    state: QueryStates,
    memoryUsed: Nat,
    startTime: Nat,
    endTime: Nat \cup {0}
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ serverState \in [ServerIds -> ServerStates]
    /\ serverUptime \in [ServerIds -> Nat]
    /\ connections \in [((ServerIds \X Nat)) -> ConnectionRecord]
    /\ connectionCount \in [ServerIds -> Nat]
    /\ queries \in [((ServerIds \X Nat)) -> QueryRecord]
    /\ queryQueue \in [ServerIds -> Seq(Nat)]
    /\ activeQueries \in [ServerIds -> SUBSET Nat]
    /\ nextQueryId \in [ServerIds -> Nat]
    /\ memoryAllocated \in [ServerIds -> Nat]
    /\ cpuUtilization \in [ServerIds -> 0..100]
    /\ diskIOPending \in [ServerIds -> Nat]
    /\ activeTxns \in [ServerIds -> SUBSET Nat]
    /\ preparedTxns \in [ServerIds -> SUBSET Nat]
    /\ totalQueriesProcessed \in [ServerIds -> Nat]
    /\ totalConnections \in [ServerIds -> Nat]
    /\ totalErrors \in [ServerIds -> Nat]

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ serverState = [s \in ServerIds |-> "STARTING"]
    /\ serverUptime = [s \in ServerIds |-> 0]
    /\ connections = [x \in {} |-> {}]
    /\ connectionCount = [s \in ServerIds |-> 0]
    /\ queries = [x \in {} |-> {}]
    /\ queryQueue = [s \in ServerIds |-> <<>>]
    /\ activeQueries = [s \in ServerIds |-> {}]
    /\ nextQueryId = [s \in ServerIds |-> 1]
    /\ memoryAllocated = [s \in ServerIds |-> 0]
    /\ cpuUtilization = [s \in ServerIds |-> 0]
    /\ diskIOPending = [s \in ServerIds |-> 0]
    /\ activeTxns = [s \in ServerIds |-> {}]
    /\ preparedTxns = [s \in ServerIds |-> {}]
    /\ totalQueriesProcessed = [s \in ServerIds |-> 0]
    /\ totalConnections = [s \in ServerIds |-> 0]
    /\ totalErrors = [s \in ServerIds |-> 0]

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Check if server can accept connection
CanAcceptConnection(sid) ==
    /\ serverState[sid] = "RUNNING"
    /\ connectionCount[sid] < MaxConnectionsPerServer

\* Check if resources available for query
HasResourcesForQuery(sid) ==
    /\ Cardinality(activeQueries[sid]) < MaxConcurrentQueries
    /\ memoryAllocated[sid] + MaxMemoryPerQuery <= TotalServerMemory

\* Get next query from queue
NextQueuedQuery(sid) ==
    IF queryQueue[sid] = <<>>
    THEN 0
    ELSE Head(queryQueue[sid])

(***************************************************************************
 * Actions: Server Lifecycle (Hellerstein Section 1.2)
 ***************************************************************************)

\* Start server
StartServer(sid) ==
    /\ sid \in ServerIds
    /\ serverState[sid] = "STARTING"
    /\ serverState' = [serverState EXCEPT ![sid] = "RUNNING"]
    /\ UNCHANGED <<serverUptime, connVars, queryVars, resourceVars, 
                   txnVars, statsVars>>

\* Shutdown server gracefully
ShutdownServer(sid) ==
    /\ sid \in ServerIds
    /\ serverState[sid] = "RUNNING"
    /\ activeQueries[sid] = {}  \* No active queries
    /\ serverState' = [serverState EXCEPT ![sid] = "SHUTTING_DOWN"]
    /\ UNCHANGED <<serverUptime, connVars, queryVars, resourceVars, 
                   txnVars, statsVars>>

\* Complete shutdown
CompleteShutdown(sid) ==
    /\ sid \in ServerIds
    /\ serverState[sid] = "SHUTTING_DOWN"
    /\ connectionCount[sid] = 0
    /\ serverState' = [serverState EXCEPT ![sid] = "STOPPED"]
    /\ UNCHANGED <<serverUptime, connVars, queryVars, resourceVars, 
                   txnVars, statsVars>>

(***************************************************************************
 * Actions: Connection Management (Hellerstein Section 2)
 ***************************************************************************)

\* Accept new connection
AcceptConnection(sid, cid) ==
    /\ sid \in ServerIds
    /\ cid \in Nat
    /\ <<sid, cid>> \notin DOMAIN connections
    /\ CanAcceptConnection(sid)
    /\ LET conn == [
           cid |-> cid,
           state |-> "ACTIVE",
           txnId |-> 0,
           startTime |-> serverUptime[sid],
           lastActivity |-> serverUptime[sid],
           authenticated |-> TRUE
       ]
       IN
        /\ connections' = connections @@ (<<sid, cid>> :> conn)
        /\ connectionCount' = [connectionCount EXCEPT ![sid] = @ + 1]
        /\ totalConnections' = [totalConnections EXCEPT ![sid] = @ + 1]
        /\ UNCHANGED <<serverVars, queryVars, resourceVars, txnVars,
                       totalQueriesProcessed, totalErrors>>

\* Close connection
CloseConnection(sid, cid) ==
    /\ sid \in ServerIds
    /\ <<sid, cid>> \in DOMAIN connections
    /\ LET conn == connections[<<sid, cid>>]
       IN
        /\ conn.state \in {"ACTIVE", "IDLE"}
        /\ conn.txnId = 0  \* Not in transaction
        /\ connections' = [x \in DOMAIN connections \ {<<sid, cid>>} |-> 
                          connections[x]]
        /\ connectionCount' = [connectionCount EXCEPT ![sid] = @ - 1]
        /\ UNCHANGED <<serverVars, queryVars, resourceVars, txnVars, statsVars>>

(***************************************************************************
 * Actions: Query Processing (Hellerstein Section 4)
 ***************************************************************************)

\* Submit query
SubmitQuery(sid, cid, qtype) ==
    /\ sid \in ServerIds
    /\ <<sid, cid>> \in DOMAIN connections
    /\ qtype \in QueryTypes
    /\ serverState[sid] = "RUNNING"
    /\ LET qid == nextQueryId[sid]
           query == [
               qid |-> qid,
               cid |-> cid,
               type |-> qtype,
               state |-> "QUEUED",
               memoryUsed |-> 0,
               startTime |-> serverUptime[sid],
               endTime |-> 0
           ]
       IN
        /\ queries' = queries @@ (<<sid, qid>> :> query)
        /\ queryQueue' = [queryQueue EXCEPT ![sid] = Append(@, qid)]
        /\ nextQueryId' = [nextQueryId EXCEPT ![sid] = @ + 1]
        /\ UNCHANGED <<serverVars, connVars, activeQueries, resourceVars,
                       txnVars, statsVars>>

\* Start query execution (admission control)
StartQueryExecution(sid) ==
    /\ sid \in ServerIds
    /\ serverState[sid] = "RUNNING"
    /\ HasResourcesForQuery(sid)
    /\ LET qid == NextQueuedQuery(sid)
       IN
        /\ qid # 0
        /\ <<sid, qid>> \in DOMAIN queries
        /\ queries[<<sid, qid>>].state = "QUEUED"
        /\ queries' = [queries EXCEPT 
            ![<<sid, qid>>].state = "EXECUTING",
            ![<<sid, qid>>].memoryUsed = MaxMemoryPerQuery
           ]
        /\ queryQueue' = [queryQueue EXCEPT ![sid] = Tail(@)]
        /\ activeQueries' = [activeQueries EXCEPT ![sid] = @ \cup {qid}]
        /\ memoryAllocated' = [memoryAllocated EXCEPT 
            ![sid] = @ + MaxMemoryPerQuery]
        /\ UNCHANGED <<serverVars, connVars, nextQueryId, cpuUtilization,
                       diskIOPending, txnVars, statsVars>>

\* Complete query execution
CompleteQueryExecution(sid, qid, success) ==
    /\ sid \in ServerIds
    /\ qid \in activeQueries[sid]
    /\ <<sid, qid>> \in DOMAIN queries
    /\ queries[<<sid, qid>>].state = "EXECUTING"
    /\ LET query == queries[<<sid, qid>>]
           newState == IF success THEN "COMPLETED" ELSE "FAILED"
       IN
        /\ queries' = [queries EXCEPT 
            ![<<sid, qid>>].state = newState,
            ![<<sid, qid>>].endTime = serverUptime[sid]
           ]
        /\ activeQueries' = [activeQueries EXCEPT ![sid] = @ \ {qid}]
        /\ memoryAllocated' = [memoryAllocated EXCEPT 
            ![sid] = @ - query.memoryUsed]
        /\ totalQueriesProcessed' = [totalQueriesProcessed EXCEPT ![sid] = @ + 1]
        /\ IF success
           THEN totalErrors' = totalErrors
           ELSE totalErrors' = [totalErrors EXCEPT ![sid] = @ + 1]
        /\ UNCHANGED <<serverVars, connVars, queryQueue, nextQueryId,
                       cpuUtilization, diskIOPending, txnVars, totalConnections>>

(***************************************************************************
 * Actions: Transaction Management
 ***************************************************************************)

\* Begin transaction
BeginTransaction(sid, cid, txnId) ==
    /\ sid \in ServerIds
    /\ <<sid, cid>> \in DOMAIN connections
    /\ txnId \in Nat
    /\ connections[<<sid, cid>>].txnId = 0
    /\ connections' = [connections EXCEPT 
        ![<<sid, cid>>].txnId = txnId,
        ![<<sid, cid>>].state = "IN_TRANSACTION"
       ]
    /\ activeTxns' = [activeTxns EXCEPT ![sid] = @ \cup {txnId}]
    /\ UNCHANGED <<serverVars, connectionCount, queryVars, resourceVars,
                   preparedTxns, statsVars>>

\* Commit transaction
CommitTransaction(sid, cid, txnId) ==
    /\ sid \in ServerIds
    /\ <<sid, cid>> \in DOMAIN connections
    /\ connections[<<sid, cid>>].txnId = txnId
    /\ txnId \in activeTxns[sid]
    /\ connections' = [connections EXCEPT 
        ![<<sid, cid>>].txnId = 0,
        ![<<sid, cid>>].state = "ACTIVE"
       ]
    /\ activeTxns' = [activeTxns EXCEPT ![sid] = @ \ {txnId}]
    /\ UNCHANGED <<serverVars, connectionCount, queryVars, resourceVars,
                   preparedTxns, statsVars>>

\* Abort transaction
AbortTransaction(sid, cid, txnId) ==
    /\ sid \in ServerIds
    /\ <<sid, cid>> \in DOMAIN connections
    /\ connections[<<sid, cid>>].txnId = txnId
    /\ txnId \in activeTxns[sid]
    /\ connections' = [connections EXCEPT 
        ![<<sid, cid>>].txnId = 0,
        ![<<sid, cid>>].state = "ACTIVE"
       ]
    /\ activeTxns' = [activeTxns EXCEPT ![sid] = @ \ {txnId}]
    /\ totalErrors' = [totalErrors EXCEPT ![sid] = @ + 1]
    /\ UNCHANGED <<serverVars, connectionCount, queryVars, resourceVars,
                   preparedTxns, totalQueriesProcessed, totalConnections>>

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E s \in ServerIds : StartServer(s)
    \/ \E s \in ServerIds : ShutdownServer(s)
    \/ \E s \in ServerIds : CompleteShutdown(s)
    \/ \E s \in ServerIds, c \in Nat : AcceptConnection(s, c)
    \/ \E s \in ServerIds, c \in Nat : CloseConnection(s, c)
    \/ \E s \in ServerIds, c \in Nat, qt \in QueryTypes : 
        SubmitQuery(s, c, qt)
    \/ \E s \in ServerIds : StartQueryExecution(s)
    \/ \E s \in ServerIds, q \in Nat, success \in BOOLEAN :
        CompleteQueryExecution(s, q, success)
    \/ \E s \in ServerIds, c \in Nat, t \in Nat : BeginTransaction(s, c, t)
    \/ \E s \in ServerIds, c \in Nat, t \in Nat : CommitTransaction(s, c, t)
    \/ \E s \in ServerIds, c \in Nat, t \in Nat : AbortTransaction(s, c, t)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (Hellerstein Section 1.3)
 ***************************************************************************)

\* Connection limit enforced
ConnectionLimitEnforced ==
    \A s \in ServerIds : connectionCount[s] <= MaxConnectionsPerServer

\* Concurrent query limit enforced
ConcurrentQueryLimitEnforced ==
    \A s \in ServerIds : Cardinality(activeQueries[s]) <= MaxConcurrentQueries

\* Memory limit enforced
MemoryLimitEnforced ==
    \A s \in ServerIds : memoryAllocated[s] <= TotalServerMemory

\* Active queries have allocated memory
ActiveQueriesHaveMemory ==
    \A s \in ServerIds, q \in activeQueries[s] :
        <<s, q>> \in DOMAIN queries =>
            queries[<<s, q>>].memoryUsed > 0

\* Transactions belong to connections
TransactionsBelongToConnections ==
    \A s \in ServerIds, t \in activeTxns[s] :
        \E c \in Nat : 
            <<s, c>> \in DOMAIN connections /\ 
            connections[<<s, c>>].txnId = t

Safety ==
    /\ ConnectionLimitEnforced
    /\ ConcurrentQueryLimitEnforced
    /\ MemoryLimitEnforced
    /\ ActiveQueriesHaveMemory
    /\ TransactionsBelongToConnections

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Queued queries eventually execute
QueriesEventuallyExecute ==
    \A s \in ServerIds, q \in Nat :
        (<<s, q>> \in DOMAIN queries /\ queries[<<s, q>>].state = "QUEUED")
            ~> (queries[<<s, q>>].state \in {"EXECUTING", "COMPLETED", "FAILED"})

\* Active queries eventually complete
QueriesEventuallyComplete ==
    \A s \in ServerIds, q \in activeQueries[s] :
        <>( q \notin activeQueries[s])

\* Transactions eventually terminate
TransactionsEventuallyTerminate ==
    \A s \in ServerIds, t \in activeTxns[s] :
        <>(t \notin activeTxns[s])

Liveness ==
    /\ QueriesEventuallyExecute
    /\ QueriesEventuallyComplete
    /\ TransactionsEventuallyTerminate

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []Liveness

================================================================================

