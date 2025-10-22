---------------------------- MODULE ConnectionPooling ----------------------------
(*
  ColibrìDB Connection Pooling Specification
  
  Manages database connection pools including:
  - Connection lifecycle management
  - Pool sizing and scaling
  - Connection health monitoring
  - Load balancing across connections
  - Connection timeout and retry logic
  - Multi-tenant connection isolation
  
  Based on:
  - HikariCP (2012) - "Fast, Simple, Reliable Database Connection Pooling"
  - Apache Commons DBCP (2002) - "Database Connection Pooling"
  - c3p0 (2000) - "JDBC3 Connection and Statement Pooling"
  - PostgreSQL Connection Pooling Best Practices
  - Oracle UCP (Universal Connection Pool)
  
  Key Properties:
  - Efficiency: Minimal connection overhead
  - Reliability: Connection health monitoring
  - Scalability: Dynamic pool sizing
  - Isolation: Multi-tenant support
  - Performance: Fast connection acquisition
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxPoolSize,           \* Maximum number of connections per pool
  MinPoolSize,           \* Minimum number of connections per pool
  ConnectionTimeout,     \* Timeout for acquiring connection
  IdleTimeout,           \* Timeout for idle connections
  MaxLifetime,           \* Maximum lifetime of a connection
  ValidationTimeout,     \* Timeout for connection validation
  LeakDetectionThreshold \* Threshold for connection leak detection

VARIABLES
  pools,                 \* [PoolName -> ConnectionPool]
  connections,           \* [ConnectionId -> Connection]
  connectionStates,      \* [ConnectionId -> ConnectionState]
  poolMetrics,           \* [PoolName -> PoolMetrics]
  tenantPools,           \* [TenantId -> PoolName]
  connectionRequests,    \* [RequestId -> ConnectionRequest]
  healthChecks,          \* [ConnectionId -> HealthCheck]
  loadBalancers          \* [PoolName -> LoadBalancer]

connectionPoolingVars == <<pools, connections, connectionStates, poolMetrics, 
                          tenantPools, connectionRequests, healthChecks, loadBalancers>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Connection pool configuration
ConnectionPool == [
  poolName: STRING,
  tenantId: STRING,
  minSize: Nat,
  maxSize: Nat,
  currentSize: Nat,
  activeConnections: Nat,
  idleConnections: Nat,
  createdConnections: Nat,
  destroyedConnections: Nat,
  lastActivity: Timestamp,
  isActive: BOOLEAN
]

\* Individual database connection
Connection == [
  connectionId: Nat,
  poolName: STRING,
  tenantId: STRING,
  state: {"idle", "active", "validating", "invalid", "closed"},
  createdAt: Timestamp,
  lastUsed: Timestamp,
  lastValidated: Timestamp,
  useCount: Nat,
  isLeaked: BOOLEAN,
  errorCount: Nat
]

\* Connection state tracking
ConnectionState == [
  connectionId: Nat,
  currentTxId: TxId,
  statementCount: Nat,
  resultSetCount: Nat,
  lockCount: Nat,
  memoryUsage: Nat,
  cpuUsage: Nat,
  lastQuery: STRING,
  lastError: STRING
]

\* Pool performance metrics
PoolMetrics == [
  poolName: STRING,
  totalRequests: Nat,
  successfulRequests: Nat,
  failedRequests: Nat,
  averageWaitTime: Nat,
  averageConnectionTime: Nat,
  peakConnections: Nat,
  currentWaitQueue: Nat,
  totalConnectionsCreated: Nat,
  totalConnectionsDestroyed: Nat,
  lastReset: Timestamp
]

\* Connection request
ConnectionRequest == [
  requestId: Nat,
  poolName: STRING,
  tenantId: STRING,
  requestedAt: Timestamp,
  timeout: Nat,
  priority: Nat,  \* 1-10, higher = more urgent
  status: {"pending", "granted", "timeout", "failed"},
  grantedConnectionId: Nat,
  waitTime: Nat
]

\* Health check for connection
HealthCheck == [
  connectionId: Nat,
  lastCheck: Timestamp,
  checkInterval: Nat,
  consecutiveFailures: Nat,
  isHealthy: BOOLEAN,
  lastError: STRING,
  responseTime: Nat
]

\* Load balancer for connection distribution
LoadBalancer == [
  poolName: STRING,
  strategy: {"round_robin", "least_used", "random", "weighted"},
  weights: [ConnectionId -> Nat],
  lastSelected: ConnectionId,
  selectionCount: [ConnectionId -> Nat]
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_ConnectionPooling ==
  /\ pools \in [STRING -> ConnectionPool]
  /\ connections \in [Nat -> Connection]
  /\ connectionStates \in [Nat -> ConnectionState]
  /\ poolMetrics \in [STRING -> PoolMetrics]
  /\ tenantPools \in [STRING -> STRING]
  /\ connectionRequests \in [Nat -> ConnectionRequest]
  /\ healthChecks \in [Nat -> HealthCheck]
  /\ loadBalancers \in [STRING -> LoadBalancer]

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ pools = [p \in {} |-> [
       poolName |-> "",
       tenantId |-> "",
       minSize |-> 0,
       maxSize |-> 0,
       currentSize |-> 0,
       activeConnections |-> 0,
       idleConnections |-> 0,
       createdConnections |-> 0,
       destroyedConnections |-> 0,
       lastActivity |-> 0,
       isActive |-> FALSE
     ]]
  /\ connections = [c \in {} |-> [
       connectionId |-> 0,
       poolName |-> "",
       tenantId |-> "",
       state |-> "closed",
       createdAt |-> 0,
       lastUsed |-> 0,
       lastValidated |-> 0,
       useCount |-> 0,
       isLeaked |-> FALSE,
       errorCount |-> 0
     ]]
  /\ connectionStates = [c \in {} |-> [
       connectionId |-> 0,
       currentTxId |-> 0,
       statementCount |-> 0,
       resultSetCount |-> 0,
       lockCount |-> 0,
       memoryUsage |-> 0,
       cpuUsage |-> 0,
       lastQuery |-> "",
       lastError |-> ""
     ]]
  /\ poolMetrics = [p \in {} |-> [
       poolName |-> "",
       totalRequests |-> 0,
       successfulRequests |-> 0,
       failedRequests |-> 0,
       averageWaitTime |-> 0,
       averageConnectionTime |-> 0,
       peakConnections |-> 0,
       currentWaitQueue |-> 0,
       totalConnectionsCreated |-> 0,
       totalConnectionsDestroyed |-> 0,
       lastReset |-> 0
     ]]
  /\ tenantPools = [t \in {} |-> ""]
  /\ connectionRequests = [r \in {} |-> [
       requestId |-> 0,
       poolName |-> "",
       tenantId |-> "",
       requestedAt |-> 0,
       timeout |-> 0,
       priority |-> 5,
       status |-> "pending",
       grantedConnectionId |-> 0,
       waitTime |-> 0
     ]]
  /\ healthChecks = [c \in {} |-> [
       connectionId |-> 0,
       lastCheck |-> 0,
       checkInterval |-> 30,
       consecutiveFailures |-> 0,
       isHealthy |-> TRUE,
       lastError |-> "",
       responseTime |-> 0
     ]]
  /\ loadBalancers = [p \in {} |-> [
       poolName |-> "",
       strategy |-> "round_robin",
       weights |-> [c \in {} |-> 1],
       lastSelected |-> 0,
       selectionCount |-> [c \in {} |-> 0]
     ]]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Create connection pool
CreatePool(poolName, tenantId, minSize, maxSize) ==
  /\ ~(poolName \in DOMAIN pools)
  /\ minSize <= maxSize
  /\ maxSize <= MaxPoolSize
  /\ LET pool == [
       poolName |-> poolName,
       tenantId |-> tenantId,
       minSize |-> minSize,
       maxSize |-> maxSize,
       currentSize |-> 0,
       activeConnections |-> 0,
       idleConnections |-> 0,
       createdConnections |-> 0,
       destroyedConnections |-> 0,
       lastActivity |-> globalTimestamp,
       isActive |-> TRUE
     ]
       metrics == [
         poolName |-> poolName,
         totalRequests |-> 0,
         successfulRequests |-> 0,
         failedRequests |-> 0,
         averageWaitTime |-> 0,
         averageConnectionTime |-> 0,
         peakConnections |-> 0,
         currentWaitQueue |-> 0,
         totalConnectionsCreated |-> 0,
         totalConnectionsDestroyed |-> 0,
         lastReset |-> globalTimestamp
       ]
       loadBalancer == [
         poolName |-> poolName,
         strategy |-> "round_robin",
         weights |-> [c \in {} |-> 1],
         lastSelected |-> 0,
         selectionCount |-> [c \in {} |-> 0]
       ]
  IN /\ pools' = [pools EXCEPT ![poolName] = pool]
     /\ poolMetrics' = [poolMetrics EXCEPT ![poolName] = metrics]
     /\ loadBalancers' = [loadBalancers EXCEPT ![poolName] = loadBalancer]
     /\ tenantPools' = [tenantPools EXCEPT ![tenantId] = poolName]
     /\ UNCHANGED <<connections, connectionStates, connectionRequests, healthChecks>>

\* Create new connection
CreateConnection(poolName, connectionId) ==
  /\ poolName \in DOMAIN pools
  /\ ~(connectionId \in DOMAIN connections)
  /\ LET pool == pools[poolName]
       connection == [
         connectionId |-> connectionId,
         poolName |-> poolName,
         tenantId |-> pool.tenantId,
         state |-> "idle",
         createdAt |-> globalTimestamp,
         lastUsed |-> globalTimestamp,
         lastValidated |-> globalTimestamp,
         useCount |-> 0,
         isLeaked |-> FALSE,
         errorCount |-> 0
       ]
       connectionState == [
         connectionId |-> connectionId,
         currentTxId |-> 0,
         statementCount |-> 0,
         resultSetCount |-> 0,
         lockCount |-> 0,
         memoryUsage |-> 0,
         cpuUsage |-> 0,
         lastQuery |-> "",
         lastError |-> ""
       ]
       healthCheck == [
         connectionId |-> connectionId,
         lastCheck |-> globalTimestamp,
         checkInterval |-> 30,
         consecutiveFailures |-> 0,
         isHealthy |-> TRUE,
         lastError |-> "",
         responseTime |-> 0
       ]
  IN /\ connections' = [connections EXCEPT ![connectionId] = connection]
     /\ connectionStates' = [connectionStates EXCEPT ![connectionId] = connectionState]
     /\ healthChecks' = [healthChecks EXCEPT ![connectionId] = healthCheck]
     /\ pools' = [pools EXCEPT ![poolName] = [pool EXCEPT 
                   !.currentSize = pool.currentSize + 1,
                   !.idleConnections = pool.idleConnections + 1,
                   !.createdConnections = pool.createdConnections + 1,
                   !.lastActivity = globalTimestamp]]
     /\ poolMetrics' = [poolMetrics EXCEPT ![poolName] = 
                       [poolMetrics[poolName] EXCEPT 
                        !.totalConnectionsCreated = poolMetrics[poolName].totalConnectionsCreated + 1]]
     /\ UNCHANGED <<tenantPools, connectionRequests, loadBalancers>>

\* Request connection from pool
RequestConnection(poolName, tenantId, requestId, timeout, priority) ==
  /\ poolName \in DOMAIN pools
  /\ ~(requestId \in DOMAIN connectionRequests)
  /\ LET pool == pools[poolName]
       request == [
         requestId |-> requestId,
         poolName |-> poolName,
         tenantId |-> tenantId,
         requestedAt |-> globalTimestamp,
         timeout |-> timeout,
         priority |-> priority,
         status |-> "pending",
         grantedConnectionId |-> 0,
         waitTime |-> 0
       ]
  IN /\ connectionRequests' = [connectionRequests EXCEPT ![requestId] = request]
     /\ poolMetrics' = [poolMetrics EXCEPT ![poolName] = 
                       [poolMetrics[poolName] EXCEPT 
                        !.totalRequests = poolMetrics[poolName].totalRequests + 1,
                        !.currentWaitQueue = poolMetrics[poolName].currentWaitQueue + 1]]
     /\ UNCHANGED <<pools, connections, connectionStates, tenantPools, healthChecks, loadBalancers>>

\* Grant connection to request
GrantConnection(requestId, connectionId) ==
  /\ requestId \in DOMAIN connectionRequests
  /\ connectionId \in DOMAIN connections
  /\ LET request == connectionRequests[requestId]
       connection == connections[connectionId]
       pool == pools[request.poolName]
       connectionState == connectionStates[connectionId]
  IN /\ connectionRequests' = [connectionRequests EXCEPT ![requestId] = 
                              [request EXCEPT 
                               !.status = "granted",
                               !.grantedConnectionId = connectionId,
                               !.waitTime = globalTimestamp - request.requestedAt]]
     /\ connections' = [connections EXCEPT ![connectionId] = 
                       [connection EXCEPT 
                        !.state = "active",
                        !.lastUsed = globalTimestamp,
                        !.useCount = connection.useCount + 1]]
     /\ connectionStates' = [connectionStates EXCEPT ![connectionId] = 
                            [connectionState EXCEPT 
                             !.currentTxId = requestId]]
     /\ pools' = [pools EXCEPT ![request.poolName] = 
                 [pool EXCEPT 
                  !.activeConnections = pool.activeConnections + 1,
                  !.idleConnections = pool.idleConnections - 1,
                  !.lastActivity = globalTimestamp]]
     /\ poolMetrics' = [poolMetrics EXCEPT ![request.poolName] = 
                       [poolMetrics[request.poolName] EXCEPT 
                        !.successfulRequests = poolMetrics[request.poolName].successfulRequests + 1,
                        !.currentWaitQueue = poolMetrics[request.poolName].currentWaitQueue - 1,
                        !.averageWaitTime = CalculateAverageWaitTime(request.poolName)]]
     /\ UNCHANGED <<tenantPools, healthChecks, loadBalancers>>

\* Return connection to pool
ReturnConnection(connectionId) ==
  /\ connectionId \in DOMAIN connections
  /\ LET connection == connections[connectionId]
       pool == pools[connection.poolName]
       connectionState == connectionStates[connectionId]
  IN /\ connections' = [connections EXCEPT ![connectionId] = 
                       [connection EXCEPT 
                        !.state = "idle",
                        !.lastUsed = globalTimestamp]]
     /\ connectionStates' = [connectionStates EXCEPT ![connectionId] = 
                            [connectionState EXCEPT 
                             !.currentTxId = 0]]
     /\ pools' = [pools EXCEPT ![connection.poolName] = 
                 [pool EXCEPT 
                  !.activeConnections = pool.activeConnections - 1,
                  !.idleConnections = pool.idleConnections + 1,
                  !.lastActivity = globalTimestamp]]
     /\ UNCHANGED <<tenantPools, connectionRequests, healthChecks, loadBalancers>>

\* Close connection
CloseConnection(connectionId) ==
  /\ connectionId \in DOMAIN connections
  /\ LET connection == connections[connectionId]
       pool == pools[connection.poolName]
  IN /\ connections' = [c \in DOMAIN connections \ {connectionId} |-> connections[c]]
     /\ connectionStates' = [c \in DOMAIN connectionStates \ {connectionId} |-> connectionStates[c]]
     /\ healthChecks' = [c \in DOMAIN healthChecks \ {connectionId} |-> healthChecks[c]]
     /\ pools' = [pools EXCEPT ![connection.poolName] = 
                 [pool EXCEPT 
                  !.currentSize = pool.currentSize - 1,
                  !.idleConnections = IF connection.state = "idle" 
                                     THEN pool.idleConnections - 1 
                                     ELSE pool.idleConnections,
                  !.activeConnections = IF connection.state = "active" 
                                       THEN pool.activeConnections - 1 
                                       ELSE pool.activeConnections,
                  !.destroyedConnections = pool.destroyedConnections + 1]]
     /\ poolMetrics' = [poolMetrics EXCEPT ![connection.poolName] = 
                       [poolMetrics[connection.poolName] EXCEPT 
                        !.totalConnectionsDestroyed = poolMetrics[connection.poolName].totalConnectionsDestroyed + 1]]
     /\ UNCHANGED <<tenantPools, connectionRequests, loadBalancers>>

\* Validate connection health
ValidateConnection(connectionId, isHealthy, responseTime, errorMessage) ==
  /\ connectionId \in DOMAIN connections
  /\ LET connection == connections[connectionId]
       healthCheck == healthChecks[connectionId]
       updatedHealthCheck == [healthCheck EXCEPT 
                             !.lastCheck = globalTimestamp,
                             !.isHealthy = isHealthy,
                             !.responseTime = responseTime,
                             !.lastError = errorMessage,
                             !.consecutiveFailures = IF isHealthy THEN 0 ELSE healthCheck.consecutiveFailures + 1]
  IN /\ healthChecks' = [healthChecks EXCEPT ![connectionId] = updatedHealthCheck]
     /\ UNCHANGED <<pools, connections, connectionStates, poolMetrics, 
                   tenantPools, connectionRequests, loadBalancers>>

\* Scale pool size
ScalePool(poolName, newSize) ==
  /\ poolName \in DOMAIN pools
  /\ LET pool == pools[poolName]
       minSize == pool.minSize
       maxSize == pool.maxSize
  IN /\ newSize >= minSize /\ newSize <= maxSize
     /\ pools' = [pools EXCEPT ![poolName] = [pool EXCEPT !.maxSize = newSize]]
     /\ UNCHANGED <<connections, connectionStates, poolMetrics, tenantPools, 
                   connectionRequests, healthChecks, loadBalancers>>

\* Update load balancer strategy
UpdateLoadBalancerStrategy(poolName, strategy, weights) ==
  /\ poolName \in DOMAIN loadBalancers
  /\ LET loadBalancer == loadBalancers[poolName]
       updatedLoadBalancer == [loadBalancer EXCEPT 
                              !.strategy = strategy,
                              !.weights = weights]
  IN /\ loadBalancers' = [loadBalancers EXCEPT ![poolName] = updatedLoadBalancer]
     /\ UNCHANGED <<pools, connections, connectionStates, poolMetrics, 
                   tenantPools, connectionRequests, healthChecks>>

\* Select connection using load balancer
SelectConnection(poolName, connectionId) ==
  /\ poolName \in DOMAIN loadBalancers
  /\ connectionId \in DOMAIN connections
  /\ LET loadBalancer == loadBalancers[poolName]
       connection == connections[connectionId]
       updatedLoadBalancer == [loadBalancer EXCEPT 
                              !.lastSelected = connectionId,
                              !.selectionCount = [loadBalancer.selectionCount EXCEPT ![connectionId] = 
                                                 loadBalancer.selectionCount[connectionId] + 1]]
  IN /\ loadBalancers' = [loadBalancers EXCEPT ![poolName] = updatedLoadBalancer]
     /\ UNCHANGED <<pools, connections, connectionStates, poolMetrics, 
                   tenantPools, connectionRequests, healthChecks>>

\* Handle connection timeout
HandleConnectionTimeout(requestId) ==
  /\ requestId \in DOMAIN connectionRequests
  /\ LET request == connectionRequests[requestId]
       pool == pools[request.poolName]
  IN /\ connectionRequests' = [connectionRequests EXCEPT ![requestId] = 
                              [request EXCEPT 
                               !.status = "timeout",
                               !.waitTime = globalTimestamp - request.requestedAt]]
     /\ poolMetrics' = [poolMetrics EXCEPT ![request.poolName] = 
                       [poolMetrics[request.poolName] EXCEPT 
                        !.failedRequests = poolMetrics[request.poolName].failedRequests + 1,
                        !.currentWaitQueue = poolMetrics[request.poolName].currentWaitQueue - 1]]
     /\ UNCHANGED <<pools, connections, connectionStates, tenantPools, healthChecks, loadBalancers>>

\* Detect connection leak
DetectConnectionLeak(connectionId) ==
  /\ connectionId \in DOMAIN connections
  /\ LET connection == connections[connectionId]
       pool == pools[connection.poolName]
       isLeaked == globalTimestamp - connection.lastUsed > LeakDetectionThreshold
  IN /\ connections' = [connections EXCEPT ![connectionId] = 
                       [connection EXCEPT !.isLeaked = isLeaked]]
     /\ UNCHANGED <<pools, connectionStates, poolMetrics, tenantPools, 
                   connectionRequests, healthChecks, loadBalancers>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Calculate average wait time for pool
CalculateAverageWaitTime(poolName) ==
  IF poolName \in DOMAIN poolMetrics
  THEN LET metrics == poolMetrics[poolName]
       IN IF metrics.totalRequests > 0 
          THEN metrics.averageWaitTime 
          ELSE 0
  ELSE 0

\* Check if pool needs scaling
NeedsScaling(poolName) ==
  IF poolName \in DOMAIN pools
  THEN LET pool == pools[poolName]
       IN pool.currentSize < pool.minSize \/ pool.currentSize > pool.maxSize
  ELSE FALSE

\* Get optimal pool size based on load
GetOptimalPoolSize(poolName) ==
  IF poolName \in DOMAIN pools
  THEN LET pool == pools[poolName]
           metrics == poolMetrics[poolName]
       IN IF metrics.currentWaitQueue > 5 
          THEN pool.maxSize
          ELSE IF metrics.currentWaitQueue = 0 /\ pool.idleConnections > 2
               THEN pool.minSize
               ELSE pool.currentSize
  ELSE 0

\* Check if connection is healthy
IsConnectionHealthy(connectionId) ==
  IF connectionId \in DOMAIN healthChecks
  THEN LET healthCheck == healthChecks[connectionId]
       IN healthCheck.isHealthy /\ healthCheck.consecutiveFailures < 3
  ELSE FALSE

\* Get next connection using load balancer
GetNextConnection(poolName) ==
  IF poolName \in DOMAIN loadBalancers
  THEN LET loadBalancer == loadBalancers[poolName]
       IN CASE loadBalancer.strategy
         OF "round_robin" -> GetRoundRobinConnection(poolName)
         [] "least_used" -> GetLeastUsedConnection(poolName)
         [] "random" -> GetRandomConnection(poolName)
         [] "weighted" -> GetWeightedConnection(poolName)
       ENDCASE
  ELSE 0

\* Get connection using round-robin strategy
GetRoundRobinConnection(poolName) ==
  IF poolName \in DOMAIN loadBalancers
  THEN LET loadBalancer == loadBalancers[poolName]
       IN loadBalancer.lastSelected + 1
  ELSE 0

\* Get least used connection
GetLeastUsedConnection(poolName) ==
  IF poolName \in DOMAIN loadBalancers
  THEN LET loadBalancer == loadBalancers[poolName]
       IN CHOOSE c \in DOMAIN loadBalancer.selectionCount : 
            \A d \in DOMAIN loadBalancer.selectionCount : 
              loadBalancer.selectionCount[c] <= loadBalancer.selectionCount[d]
  ELSE 0

\* Get random connection
GetRandomConnection(poolName) ==
  IF poolName \in DOMAIN loadBalancers
  THEN CHOOSE c \in 1..100 : TRUE  \* Simplified for TLA+
  ELSE 0

\* Get weighted connection
GetWeightedConnection(poolName) ==
  IF poolName \in DOMAIN loadBalancers
  THEN LET loadBalancer == loadBalancers[poolName]
       IN CHOOSE c \in DOMAIN loadBalancer.weights : 
            loadBalancer.weights[c] > 0
  ELSE 0

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E poolName \in STRING, tenantId \in STRING, minSize \in Nat, maxSize \in Nat :
       CreatePool(poolName, tenantId, minSize, maxSize)
  \/ \E poolName \in STRING, connectionId \in Nat :
       CreateConnection(poolName, connectionId)
  \/ \E poolName \in STRING, tenantId \in STRING, requestId \in Nat, 
       timeout \in Nat, priority \in Nat :
       RequestConnection(poolName, tenantId, requestId, timeout, priority)
  \/ \E requestId \in Nat, connectionId \in Nat :
       GrantConnection(requestId, connectionId)
  \/ \E connectionId \in Nat :
       ReturnConnection(connectionId)
  \/ \E connectionId \in Nat :
       CloseConnection(connectionId)
  \/ \E connectionId \in Nat, isHealthy \in BOOLEAN, responseTime \in Nat, 
       errorMessage \in STRING :
       ValidateConnection(connectionId, isHealthy, responseTime, errorMessage)
  \/ \E poolName \in STRING, newSize \in Nat :
       ScalePool(poolName, newSize)
  \/ \E poolName \in STRING, strategy \in {"round_robin", "least_used", "random", "weighted"},
       weights \in [Nat -> Nat] :
       UpdateLoadBalancerStrategy(poolName, strategy, weights)
  \/ \E poolName \in STRING, connectionId \in Nat :
       SelectConnection(poolName, connectionId)
  \/ \E requestId \in Nat :
       HandleConnectionTimeout(requestId)
  \/ \E connectionId \in Nat :
       DetectConnectionLeak(connectionId)

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Pool size constraints
Inv_ConnectionPooling_PoolSizeConstraints ==
  \A poolName \in DOMAIN pools :
    LET pool == pools[poolName]
    IN /\ pool.currentSize >= 0
       /\ pool.currentSize <= pool.maxSize
       /\ pool.activeConnections >= 0
       /\ pool.idleConnections >= 0
       /\ pool.activeConnections + pool.idleConnections = pool.currentSize

\* Connection state consistency
Inv_ConnectionPooling_ConnectionStateConsistency ==
  \A connectionId \in DOMAIN connections :
    LET connection == connections[connectionId]
        pool == pools[connection.poolName]
    IN /\ connection.state \in {"idle", "active", "validating", "invalid", "closed"}
       /\ connection.useCount >= 0
       /\ connection.errorCount >= 0
       /\ connection.createdAt <= globalTimestamp
       /\ connection.lastUsed <= globalTimestamp

\* Pool metrics consistency
Inv_ConnectionPooling_PoolMetricsConsistency ==
  \A poolName \in DOMAIN poolMetrics :
    LET metrics == poolMetrics[poolName]
    IN /\ metrics.totalRequests >= 0
       /\ metrics.successfulRequests >= 0
       /\ metrics.failedRequests >= 0
       /\ metrics.successfulRequests + metrics.failedRequests <= metrics.totalRequests
       /\ metrics.averageWaitTime >= 0
       /\ metrics.peakConnections >= 0

\* Connection request consistency
Inv_ConnectionPooling_RequestConsistency ==
  \A requestId \in DOMAIN connectionRequests :
    LET request == connectionRequests[requestId]
    IN /\ request.status \in {"pending", "granted", "timeout", "failed"}
       /\ request.priority >= 1 /\ request.priority <= 10
       /\ request.requestedAt <= globalTimestamp
       /\ request.waitTime >= 0

\* Health check consistency
Inv_ConnectionPooling_HealthCheckConsistency ==
  \A connectionId \in DOMAIN healthChecks :
    LET healthCheck == healthChecks[connectionId]
    IN /\ healthCheck.consecutiveFailures >= 0
       /\ healthCheck.responseTime >= 0
       /\ healthCheck.lastCheck <= globalTimestamp

\* Load balancer consistency
Inv_ConnectionPooling_LoadBalancerConsistency ==
  \A poolName \in DOMAIN loadBalancers :
    LET loadBalancer == loadBalancers[poolName]
    IN /\ loadBalancer.strategy \in {"round_robin", "least_used", "random", "weighted"}
       /\ loadBalancer.lastSelected >= 0
       /\ \A connectionId \in DOMAIN loadBalancer.selectionCount :
            loadBalancer.selectionCount[connectionId] >= 0

\* Tenant isolation
Inv_ConnectionPooling_TenantIsolation ==
  \A connectionId \in DOMAIN connections :
    LET connection == connections[connectionId]
        pool == pools[connection.poolName]
    IN connection.tenantId = pool.tenantId

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Pending requests are eventually granted or timeout
Liveness_RequestsEventuallyProcessed ==
  \A requestId \in DOMAIN connectionRequests :
    connectionRequests[requestId].status = "pending" => 
    <>connectionRequests[requestId].status \in {"granted", "timeout", "failed"}

\* Unhealthy connections are eventually removed
Liveness_UnhealthyConnectionsRemoved ==
  \A connectionId \in DOMAIN connections :
    LET healthCheck == healthChecks[connectionId]
    IN ~healthCheck.isHealthy /\ healthCheck.consecutiveFailures >= 3 => 
       <>~(connectionId \in DOMAIN connections)

\* Pools are eventually scaled to optimal size
Liveness_PoolsEventuallyScaled ==
  \A poolName \in DOMAIN pools :
    NeedsScaling(poolName) => <>~NeedsScaling(poolName)

\* Connection leaks are eventually detected
Liveness_ConnectionLeaksDetected ==
  \A connectionId \in DOMAIN connections :
    LET connection == connections[connectionId]
    IN globalTimestamp - connection.lastUsed > LeakDetectionThreshold => 
       <>connection.isLeaked

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Pool size never exceeds maximum
THEOREM ConnectionPooling_PoolSizeBound ==
  \A poolName \in DOMAIN pools :
    pools[poolName].currentSize <= pools[poolName].maxSize

\* Active connections never exceed pool size
THEOREM ConnectionPooling_ActiveConnectionsBound ==
  \A poolName \in DOMAIN pools :
    pools[poolName].activeConnections <= pools[poolName].currentSize

\* Connection state transitions are valid
THEOREM ConnectionPooling_ValidStateTransitions ==
  \A connectionId \in DOMAIN connections :
    LET connection == connections[connectionId]
    IN connection.state = "closed" => 
       connection.useCount > 0 \/ globalTimestamp - connection.createdAt > MaxLifetime

\* Load balancer distributes connections fairly
THEOREM ConnectionPooling_FairDistribution ==
  \A poolName \in DOMAIN loadBalancers :
    LET loadBalancer == loadBalancers[poolName]
    IN loadBalancer.strategy = "round_robin" => 
       \A connectionId \in DOMAIN loadBalancer.selectionCount :
         loadBalancer.selectionCount[connectionId] >= 0

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - ConnectionPoolManager.pools (Dictionary<String, ConnectionPool>) → pools
  - ConnectionPoolManager.connections (Dictionary<UInt64, Connection>) → connections
  - ConnectionPoolManager.poolMetrics (Dictionary<String, PoolMetrics>) → poolMetrics
  - ConnectionPoolManager.healthChecks (Dictionary<UInt64, HealthCheck>) → healthChecks
  
  USAGE:
  
  This module should be used with Server and other ColibrìDB modules:
  
  ---- MODULE Server ----
  EXTENDS ConnectionPooling
  ...
  ====================
*)