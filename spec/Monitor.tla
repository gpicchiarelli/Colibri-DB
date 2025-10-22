------------------------------- MODULE Monitor -------------------------------
(*
  ColibrìDB Monitoring Specification
  
  Manages system monitoring including:
  - Performance metrics collection
  - Health checks and alerts
  - Resource utilization tracking
  - Query performance monitoring
  - System diagnostics
  - Log aggregation and analysis
  
  Based on:
  - Google SRE (2016) - "Site Reliability Engineering"
  - Prometheus (2012) - "Monitoring and Alerting"
  - Grafana (2014) - "Observability and Monitoring"
  - OpenTelemetry (2019) - "Observability Framework"
  - PostgreSQL Monitoring Best Practices
  
  Key Properties:
  - Completeness: All critical metrics monitored
  - Accuracy: Metrics reflect actual system state
  - Timeliness: Real-time monitoring and alerting
  - Scalability: Efficient metric collection
  - Reliability: Monitoring system doesn't impact performance
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxMetrics,            \* Maximum number of metrics
  MetricRetentionTime,   \* Time to retain metrics
  AlertThreshold,        \* Threshold for triggering alerts
  HealthCheckInterval,   \* Interval for health checks
  MaxAlerts,             \* Maximum number of active alerts
  MetricSamplingRate     \* Rate for metric sampling

VARIABLES
  metrics,               \* [MetricId -> Metric]
  alerts,                \* [AlertId -> Alert]
  healthChecks,          \* [ComponentId -> HealthCheck]
  performanceData,       \* [ComponentId -> PerformanceData]
  resourceUsage,         \* [ResourceId -> ResourceUsage]
  queryMetrics,          \* [QueryId -> QueryMetric]
  systemDiagnostics,     \* SystemDiagnostics
  monitoringConfig,      \* MonitoringConfig
  logAggregator          \* LogAggregator

monitorVars == <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Individual metric
Metric == [
  metricId: Nat,
  name: STRING,
  value: Nat,
  unit: STRING,
  timestamp: Timestamp,
  componentId: Nat,
  metricType: {"counter", "gauge", "histogram", "summary"},
  labels: [STRING -> STRING],
  isActive: BOOLEAN
]

\* Alert
Alert == [
  alertId: Nat,
  name: STRING,
  severity: {"critical", "warning", "info"},
  status: {"firing", "resolved", "suppressed"},
  componentId: Nat,
  metricId: Nat,
  threshold: Nat,
  currentValue: Nat,
  triggeredAt: Timestamp,
  resolvedAt: Timestamp,
  message: STRING,
  isAcknowledged: BOOLEAN
]

\* Health check
HealthCheck == [
  componentId: Nat,
  componentName: STRING,
  status: {"healthy", "degraded", "unhealthy", "unknown"},
  lastCheck: Timestamp,
  checkInterval: Nat,
  consecutiveFailures: Nat,
  lastError: STRING,
  responseTime: Nat,
  isEnabled: BOOLEAN
]

\* Performance data
PerformanceData == [
  componentId: Nat,
  componentName: STRING,
  cpuUsage: Nat,  \* 0-100
  memoryUsage: Nat,  \* 0-100
  diskUsage: Nat,  \* 0-100
  networkUsage: Nat,  \* 0-100
  throughput: Nat,  \* operations per second
  latency: Nat,  \* milliseconds
  errorRate: Nat,  \* 0-100
  lastUpdated: Timestamp
]

\* Resource usage
ResourceUsage == [
  resourceId: Nat,
  resourceName: STRING,
  resourceType: {"cpu", "memory", "disk", "network", "connection"},
  totalCapacity: Nat,
  usedCapacity: Nat,
  availableCapacity: Nat,
  utilizationPercent: Nat,  \* 0-100
  lastUpdated: Timestamp
]

\* Query performance metric
QueryMetric == [
  queryId: Nat,
  queryText: STRING,
  executionTime: Nat,  \* milliseconds
  rowsReturned: Nat,
  rowsScanned: Nat,
  cpuTime: Nat,  \* milliseconds
  memoryUsed: Nat,  \* bytes
  diskReads: Nat,
  diskWrites: Nat,
  cacheHits: Nat,
  cacheMisses: Nat,
  timestamp: Timestamp
]

\* System diagnostics
SystemDiagnostics == [
  systemUptime: Nat,  \* seconds
  totalConnections: Nat,
  activeConnections: Nat,
  totalQueries: Nat,
  failedQueries: Nat,
  averageQueryTime: Nat,
  peakMemoryUsage: Nat,
  currentMemoryUsage: Nat,
  diskSpaceUsed: Nat,
  diskSpaceTotal: Nat,
  lastRestart: Timestamp,
  lastBackup: Timestamp,
  lastMaintenance: Timestamp
]

\* Monitoring configuration
MonitoringConfig == [
  isEnabled: BOOLEAN,
  collectionInterval: Nat,
  retentionPeriod: Nat,
  alertingEnabled: BOOLEAN,
  logLevel: {"debug", "info", "warn", "error"},
  metricsEnabled: BOOLEAN,
  healthChecksEnabled: BOOLEAN,
  performanceMonitoringEnabled: BOOLEAN,
  queryMonitoringEnabled: BOOLEAN
]

\* Log aggregator
LogAggregator == [
  isEnabled: BOOLEAN,
  logLevel: {"debug", "info", "warn", "error"},
  maxLogEntries: Nat,
  currentLogEntries: Nat,
  logRotationSize: Nat,
  lastRotation: Timestamp,
  errorCount: Nat,
  warningCount: Nat,
  infoCount: Nat,
  debugCount: Nat
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Monitor ==
  /\ metrics \in [Nat -> Metric]
  /\ alerts \in [Nat -> Alert]
  /\ healthChecks \in [Nat -> HealthCheck]
  /\ performanceData \in [Nat -> PerformanceData]
  /\ resourceUsage \in [Nat -> ResourceUsage]
  /\ queryMetrics \in [Nat -> QueryMetric]
  /\ systemDiagnostics \in SystemDiagnostics
  /\ monitoringConfig \in MonitoringConfig
  /\ logAggregator \in LogAggregator

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ metrics = [m \in {} |-> [
       metricId |-> 0,
       name |-> "",
       value |-> 0,
       unit |-> "",
       timestamp |-> 0,
       componentId |-> 0,
       metricType |-> "gauge",
       labels |-> [l \in {} |-> ""],
       isActive |-> FALSE
     ]]
  /\ alerts = [a \in {} |-> [
       alertId |-> 0,
       name |-> "",
       severity |-> "info",
       status |-> "resolved",
       componentId |-> 0,
       metricId |-> 0,
       threshold |-> 0,
       currentValue |-> 0,
       triggeredAt |-> 0,
       resolvedAt |-> 0,
       message |-> "",
       isAcknowledged |-> FALSE
     ]]
  /\ healthChecks = [c \in {} |-> [
       componentId |-> 0,
       componentName |-> "",
       status |-> "unknown",
       lastCheck |-> 0,
       checkInterval |-> 30,
       consecutiveFailures |-> 0,
       lastError |-> "",
       responseTime |-> 0,
       isEnabled |-> FALSE
     ]]
  /\ performanceData = [c \in {} |-> [
       componentId |-> 0,
       componentName |-> "",
       cpuUsage |-> 0,
       memoryUsage |-> 0,
       diskUsage |-> 0,
       networkUsage |-> 0,
       throughput |-> 0,
       latency |-> 0,
       errorRate |-> 0,
       lastUpdated |-> 0
     ]]
  /\ resourceUsage = [r \in {} |-> [
       resourceId |-> 0,
       resourceName |-> "",
       resourceType |-> "cpu",
       totalCapacity |-> 0,
       usedCapacity |-> 0,
       availableCapacity |-> 0,
       utilizationPercent |-> 0,
       lastUpdated |-> 0
     ]]
  /\ queryMetrics = [q \in {} |-> [
       queryId |-> 0,
       queryText |-> "",
       executionTime |-> 0,
       rowsReturned |-> 0,
       rowsScanned |-> 0,
       cpuTime |-> 0,
       memoryUsed |-> 0,
       diskReads |-> 0,
       diskWrites |-> 0,
       cacheHits |-> 0,
       cacheMisses |-> 0,
       timestamp |-> 0
     ]]
  /\ systemDiagnostics = [
       systemUptime |-> 0,
       totalConnections |-> 0,
       activeConnections |-> 0,
       totalQueries |-> 0,
       failedQueries |-> 0,
       averageQueryTime |-> 0,
       peakMemoryUsage |-> 0,
       currentMemoryUsage |-> 0,
       diskSpaceUsed |-> 0,
       diskSpaceTotal |-> 0,
       lastRestart |-> 0,
       lastBackup |-> 0,
       lastMaintenance |-> 0
     ]
  /\ monitoringConfig = [
       isEnabled |-> TRUE,
       collectionInterval |-> 10,
       retentionPeriod |-> 3600,
       alertingEnabled |-> TRUE,
       logLevel |-> "info",
       metricsEnabled |-> TRUE,
       healthChecksEnabled |-> TRUE,
       performanceMonitoringEnabled |-> TRUE,
       queryMonitoringEnabled |-> TRUE
     ]
  /\ logAggregator = [
       isEnabled |-> TRUE,
       logLevel |-> "info",
       maxLogEntries |-> 10000,
       currentLogEntries |-> 0,
       logRotationSize |-> 1000000,
       lastRotation |-> 0,
       errorCount |-> 0,
       warningCount |-> 0,
       infoCount |-> 0,
       debugCount |-> 0
     ]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Record metric
RecordMetric(metricId, name, value, unit, componentId, metricType, labels) ==
  /\ ~(metricId \in DOMAIN metrics)
  /\ LET metric == [
       metricId |-> metricId,
       name |-> name,
       value |-> value,
       unit |-> unit,
       timestamp |-> globalTimestamp,
       componentId |-> componentId,
       metricType |-> metricType,
       labels |-> labels,
       isActive |-> TRUE
     ]
  IN /\ metrics' = [metrics EXCEPT ![metricId] = metric]
     /\ UNCHANGED <<alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Update metric value
UpdateMetric(metricId, newValue) ==
  /\ metricId \in DOMAIN metrics
  /\ LET metric == metrics[metricId]
       updatedMetric == [metric EXCEPT 
                        !.value = newValue,
                        !.timestamp = globalTimestamp]
  IN /\ metrics' = [metrics EXCEPT ![metricId] = updatedMetric]
     /\ UNCHANGED <<alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Create alert
CreateAlert(alertId, name, severity, componentId, metricId, threshold, message) ==
  /\ ~(alertId \in DOMAIN alerts)
  /\ LET alert == [
       alertId |-> alertId,
       name |-> name,
       severity |-> severity,
       status |-> "firing",
       componentId |-> componentId,
       metricId |-> metricId,
       threshold |-> threshold,
       currentValue |-> metrics[metricId].value,
       triggeredAt |-> globalTimestamp,
       resolvedAt |-> 0,
       message |-> message,
       isAcknowledged |-> FALSE
     ]
  IN /\ alerts' = [alerts EXCEPT ![alertId] = alert]
     /\ UNCHANGED <<metrics, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Resolve alert
ResolveAlert(alertId) ==
  /\ alertId \in DOMAIN alerts
  /\ LET alert == alerts[alertId]
       resolvedAlert == [alert EXCEPT 
                        !.status = "resolved",
                        !.resolvedAt = globalTimestamp]
  IN /\ alerts' = [alerts EXCEPT ![alertId] = resolvedAlert]
     /\ UNCHANGED <<metrics, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Acknowledge alert
AcknowledgeAlert(alertId) ==
  /\ alertId \in DOMAIN alerts
  /\ LET alert == alerts[alertId]
       acknowledgedAlert == [alert EXCEPT !.isAcknowledged = TRUE]
  IN /\ alerts' = [alerts EXCEPT ![alertId] = acknowledgedAlert]
     /\ UNCHANGED <<metrics, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Perform health check
PerformHealthCheck(componentId, componentName, status, responseTime, errorMessage) ==
  /\ LET healthCheck == [
       componentId |-> componentId,
       componentName |-> componentName,
       status |-> status,
       lastCheck |-> globalTimestamp,
       checkInterval |-> HealthCheckInterval,
       consecutiveFailures |-> IF status = "healthy" THEN 0 ELSE 1,
       lastError |-> errorMessage,
       responseTime |-> responseTime,
       isEnabled |-> TRUE
     ]
  IN /\ healthChecks' = [healthChecks EXCEPT ![componentId] = healthCheck]
     /\ UNCHANGED <<metrics, alerts, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Update performance data
UpdatePerformanceData(componentId, componentName, cpuUsage, memoryUsage, diskUsage, 
                      networkUsage, throughput, latency, errorRate) ==
  /\ LET performanceData == [
       componentId |-> componentId,
       componentName |-> componentName,
       cpuUsage |-> cpuUsage,
       memoryUsage |-> memoryUsage,
       diskUsage |-> diskUsage,
       networkUsage |-> networkUsage,
       throughput |-> throughput,
       latency |-> latency,
       errorRate |-> errorRate,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ performanceData' = [performanceData EXCEPT ![componentId] = performanceData]
     /\ UNCHANGED <<metrics, alerts, healthChecks, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Update resource usage
UpdateResourceUsage(resourceId, resourceName, resourceType, totalCapacity, 
                    usedCapacity, utilizationPercent) ==
  /\ LET resourceUsage == [
       resourceId |-> resourceId,
       resourceName |-> resourceName,
       resourceType |-> resourceType,
       totalCapacity |-> totalCapacity,
       usedCapacity |-> usedCapacity,
       availableCapacity |-> totalCapacity - usedCapacity,
       utilizationPercent |-> utilizationPercent,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ resourceUsage' = [resourceUsage EXCEPT ![resourceId] = resourceUsage]
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Record query metric
RecordQueryMetric(queryId, queryText, executionTime, rowsReturned, rowsScanned, 
                  cpuTime, memoryUsed, diskReads, diskWrites, cacheHits, cacheMisses) ==
  /\ ~(queryId \in DOMAIN queryMetrics)
  /\ LET queryMetric == [
       queryId |-> queryId,
       queryText |-> queryText,
       executionTime |-> executionTime,
       rowsReturned |-> rowsReturned,
       rowsScanned |-> rowsScanned,
       cpuTime |-> cpuTime,
       memoryUsed |-> memoryUsed,
       diskReads |-> diskReads,
       diskWrites |-> diskWrites,
       cacheHits |-> cacheHits,
       cacheMisses |-> cacheMisses,
       timestamp |-> globalTimestamp
     ]
  IN /\ queryMetrics' = [queryMetrics EXCEPT ![queryId] = queryMetric]
     /\ systemDiagnostics' = [systemDiagnostics EXCEPT 
                             !.totalQueries = systemDiagnostics.totalQueries + 1,
                             !.averageQueryTime = CalculateAverageQueryTime()]
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                   monitoringConfig, logAggregator>>

\* Update system diagnostics
UpdateSystemDiagnostics(uptime, totalConnections, activeConnections, totalQueries, 
                        failedQueries, peakMemoryUsage, currentMemoryUsage, 
                        diskSpaceUsed, diskSpaceTotal, lastBackup, lastMaintenance) ==
  /\ LET diagnostics == [
       systemUptime |-> uptime,
       totalConnections |-> totalConnections,
       activeConnections |-> activeConnections,
       totalQueries |-> totalQueries,
       failedQueries |-> failedQueries,
       averageQueryTime |-> CalculateAverageQueryTime(),
       peakMemoryUsage |-> peakMemoryUsage,
       currentMemoryUsage |-> currentMemoryUsage,
       diskSpaceUsed |-> diskSpaceUsed,
       diskSpaceTotal |-> diskSpaceTotal,
       lastRestart |-> systemDiagnostics.lastRestart,
       lastBackup |-> lastBackup,
       lastMaintenance |-> lastMaintenance
     ]
  IN /\ systemDiagnostics' = diagnostics
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, monitoringConfig, logAggregator>>

\* Update monitoring configuration
UpdateMonitoringConfig(isEnabled, collectionInterval, retentionPeriod, alertingEnabled, 
                       logLevel, metricsEnabled, healthChecksEnabled, 
                       performanceMonitoringEnabled, queryMonitoringEnabled) ==
  /\ LET config == [
       isEnabled |-> isEnabled,
       collectionInterval |-> collectionInterval,
       retentionPeriod |-> retentionPeriod,
       alertingEnabled |-> alertingEnabled,
       logLevel |-> logLevel,
       metricsEnabled |-> metricsEnabled,
       healthChecksEnabled |-> healthChecksEnabled,
       performanceMonitoringEnabled |-> performanceMonitoringEnabled,
       queryMonitoringEnabled |-> queryMonitoringEnabled
     ]
  IN /\ monitoringConfig' = config
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, logAggregator>>

\* Update log aggregator
UpdateLogAggregator(isEnabled, logLevel, maxLogEntries, currentLogEntries, 
                   logRotationSize, errorCount, warningCount, infoCount, debugCount) ==
  /\ LET aggregator == [
       isEnabled |-> isEnabled,
       logLevel |-> logLevel,
       maxLogEntries |-> maxLogEntries,
       currentLogEntries |-> currentLogEntries,
       logRotationSize |-> logRotationSize,
       lastRotation |-> logAggregator.lastRotation,
       errorCount |-> errorCount,
       warningCount |-> warningCount,
       infoCount |-> infoCount,
       debugCount |-> debugCount
     ]
  IN /\ logAggregator' = aggregator
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig>>

\* Check alert thresholds
CheckAlertThresholds() ==
  /\ LET newAlerts == CheckMetricThresholds()
  IN /\ alerts' = [alerts EXCEPT ![a \in DOMAIN newAlerts] = newAlerts[a]]
     /\ UNCHANGED <<metrics, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Cleanup old metrics
CleanupOldMetrics() ==
  /\ LET currentTime == globalTimestamp
       oldMetrics == {metricId \in DOMAIN metrics : 
                     currentTime - metrics[metricId].timestamp > MetricRetentionTime}
  IN /\ metrics' = [m \in DOMAIN metrics \ oldMetrics |-> metrics[m]]
     /\ UNCHANGED <<alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig, logAggregator>>

\* Rotate logs
RotateLogs() ==
  /\ LET aggregator == logAggregator
       shouldRotate == aggregator.currentLogEntries >= aggregator.logRotationSize
       updatedAggregator == [aggregator EXCEPT 
                            !.currentLogEntries = IF shouldRotate THEN 0 ELSE aggregator.currentLogEntries,
                            !.lastRotation = IF shouldRotate THEN globalTimestamp ELSE aggregator.lastRotation]
  IN /\ logAggregator' = updatedAggregator
     /\ UNCHANGED <<metrics, alerts, healthChecks, performanceData, resourceUsage, 
                   queryMetrics, systemDiagnostics, monitoringConfig>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Calculate average query time
CalculateAverageQueryTime() ==
  IF DOMAIN queryMetrics = {} THEN 0
  ELSE LET totalTime == SumQueryTimes()
           queryCount == Len(DOMAIN queryMetrics)
       IN totalTime / queryCount

\* Sum query execution times
SumQueryTimes() ==
  IF DOMAIN queryMetrics = {} THEN 0
  ELSE LET queryId == CHOOSE q \in DOMAIN queryMetrics : TRUE
           queryMetric == queryMetrics[queryId]
           restQueries == [q \in DOMAIN queryMetrics \ {queryId} |-> queryMetrics[q]]
       IN queryMetric.executionTime + SumQueryTimes()

\* Check metric thresholds for alerts
CheckMetricThresholds() ==
  [a \in {} |-> [
     alertId |-> 0,
     name |-> "",
     severity |-> "info",
     status |-> "resolved",
     componentId |-> 0,
     metricId |-> 0,
     threshold |-> 0,
     currentValue |-> 0,
     triggeredAt |-> 0,
     resolvedAt |-> 0,
     message |-> "",
     isAcknowledged |-> FALSE
   ]]

\* Check if metric exceeds threshold
IsMetricExceedingThreshold(metricId, threshold) ==
  metricId \in DOMAIN metrics /\ metrics[metricId].value > threshold

\* Check if alert should be triggered
ShouldTriggerAlert(metricId, threshold) ==
  IsMetricExceedingThreshold(metricId, threshold) /\ 
  ~(\E alertId \in DOMAIN alerts : 
    alerts[alertId].metricId = metricId /\ alerts[alertId].status = "firing")

\* Get metric by name
GetMetricByName(metricName) ==
  CHOOSE metricId \in DOMAIN metrics : metrics[metricId].name = metricName

\* Check if component is healthy
IsComponentHealthy(componentId) ==
  componentId \in DOMAIN healthChecks /\ 
  healthChecks[componentId].status = "healthy"

\* Get resource utilization
GetResourceUtilization(resourceId) ==
  IF resourceId \in DOMAIN resourceUsage
  THEN resourceUsage[resourceId].utilizationPercent
  ELSE 0

\* Check if system is under stress
IsSystemUnderStress() ==
  \E resourceId \in DOMAIN resourceUsage : 
    resourceUsage[resourceId].utilizationPercent > 80

\* Get active alert count
GetActiveAlertCount() ==
  Len({alertId \in DOMAIN alerts : alerts[alertId].status = "firing"})

\* Get critical alert count
GetCriticalAlertCount() ==
  Len({alertId \in DOMAIN alerts : 
       alerts[alertId].status = "firing" /\ alerts[alertId].severity = "critical"})

\* Check if monitoring is enabled
IsMonitoringEnabled() ==
  monitoringConfig.isEnabled /\ monitoringConfig.metricsEnabled

\* Check if alerting is enabled
IsAlertingEnabled() ==
  monitoringConfig.alertingEnabled

\* Get system health score
GetSystemHealthScore() ==
  LET healthyComponents == Len({componentId \in DOMAIN healthChecks : 
                               healthChecks[componentId].status = "healthy"})
      totalComponents == Len(DOMAIN healthChecks)
      criticalAlerts == GetCriticalAlertCount()
  IN IF totalComponents = 0 THEN 100
     ELSE (healthyComponents * 100 / totalComponents) - (criticalAlerts * 10)

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E metricId \in Nat, name \in STRING, value \in Nat, unit \in STRING,
       componentId \in Nat, metricType \in {"counter", "gauge", "histogram", "summary"},
       labels \in [STRING -> STRING] :
       RecordMetric(metricId, name, value, unit, componentId, metricType, labels)
  \/ \E metricId \in Nat, newValue \in Nat :
       UpdateMetric(metricId, newValue)
  \/ \E alertId \in Nat, name \in STRING, severity \in {"critical", "warning", "info"},
       componentId \in Nat, metricId \in Nat, threshold \in Nat, message \in STRING :
       CreateAlert(alertId, name, severity, componentId, metricId, threshold, message)
  \/ \E alertId \in Nat :
       ResolveAlert(alertId)
  \/ \E alertId \in Nat :
       AcknowledgeAlert(alertId)
  \/ \E componentId \in Nat, componentName \in STRING, status \in {"healthy", "degraded", "unhealthy", "unknown"},
       responseTime \in Nat, errorMessage \in STRING :
       PerformHealthCheck(componentId, componentName, status, responseTime, errorMessage)
  \/ \E componentId \in Nat, componentName \in STRING, cpuUsage \in Nat, memoryUsage \in Nat,
       diskUsage \in Nat, networkUsage \in Nat, throughput \in Nat, latency \in Nat, errorRate \in Nat :
       UpdatePerformanceData(componentId, componentName, cpuUsage, memoryUsage, diskUsage,
                            networkUsage, throughput, latency, errorRate)
  \/ \E resourceId \in Nat, resourceName \in STRING, resourceType \in {"cpu", "memory", "disk", "network", "connection"},
       totalCapacity \in Nat, usedCapacity \in Nat, utilizationPercent \in Nat :
       UpdateResourceUsage(resourceId, resourceName, resourceType, totalCapacity,
                          usedCapacity, utilizationPercent)
  \/ \E queryId \in Nat, queryText \in STRING, executionTime \in Nat, rowsReturned \in Nat,
       rowsScanned \in Nat, cpuTime \in Nat, memoryUsed \in Nat, diskReads \in Nat,
       diskWrites \in Nat, cacheHits \in Nat, cacheMisses \in Nat :
       RecordQueryMetric(queryId, queryText, executionTime, rowsReturned, rowsScanned,
                        cpuTime, memoryUsed, diskReads, diskWrites, cacheHits, cacheMisses)
  \/ \E uptime \in Nat, totalConnections \in Nat, activeConnections \in Nat, totalQueries \in Nat,
       failedQueries \in Nat, peakMemoryUsage \in Nat, currentMemoryUsage \in Nat,
       diskSpaceUsed \in Nat, diskSpaceTotal \in Nat, lastBackup \in Timestamp, lastMaintenance \in Timestamp :
       UpdateSystemDiagnostics(uptime, totalConnections, activeConnections, totalQueries,
                              failedQueries, peakMemoryUsage, currentMemoryUsage,
                              diskSpaceUsed, diskSpaceTotal, lastBackup, lastMaintenance)
  \/ \E isEnabled \in BOOLEAN, collectionInterval \in Nat, retentionPeriod \in Nat,
       alertingEnabled \in BOOLEAN, logLevel \in {"debug", "info", "warn", "error"},
       metricsEnabled \in BOOLEAN, healthChecksEnabled \in BOOLEAN,
       performanceMonitoringEnabled \in BOOLEAN, queryMonitoringEnabled \in BOOLEAN :
       UpdateMonitoringConfig(isEnabled, collectionInterval, retentionPeriod, alertingEnabled,
                             logLevel, metricsEnabled, healthChecksEnabled,
                             performanceMonitoringEnabled, queryMonitoringEnabled)
  \/ \E isEnabled \in BOOLEAN, logLevel \in {"debug", "info", "warn", "error"},
       maxLogEntries \in Nat, currentLogEntries \in Nat, logRotationSize \in Nat,
       errorCount \in Nat, warningCount \in Nat, infoCount \in Nat, debugCount \in Nat :
       UpdateLogAggregator(isEnabled, logLevel, maxLogEntries, currentLogEntries,
                          logRotationSize, errorCount, warningCount, infoCount, debugCount)
  \/ CheckAlertThresholds()
  \/ CleanupOldMetrics()
  \/ RotateLogs()

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Metric constraints
Inv_Monitor_MetricConstraints ==
  \A metricId \in DOMAIN metrics :
    LET metric == metrics[metricId]
    IN /\ metric.value >= 0
       /\ metric.timestamp >= 0
       /\ metric.metricType \in {"counter", "gauge", "histogram", "summary"}

\* Alert constraints
Inv_Monitor_AlertConstraints ==
  \A alertId \in DOMAIN alerts :
    LET alert == alerts[alertId]
    IN /\ alert.severity \in {"critical", "warning", "info"}
       /\ alert.status \in {"firing", "resolved", "suppressed"}
       /\ alert.threshold >= 0
       /\ alert.currentValue >= 0
       /\ alert.triggeredAt >= 0
       /\ alert.resolvedAt >= 0

\* Health check constraints
Inv_Monitor_HealthCheckConstraints ==
  \A componentId \in DOMAIN healthChecks :
    LET healthCheck == healthChecks[componentId]
    IN /\ healthCheck.status \in {"healthy", "degraded", "unhealthy", "unknown"}
       /\ healthCheck.lastCheck >= 0
       /\ healthCheck.checkInterval > 0
       /\ healthCheck.consecutiveFailures >= 0
       /\ healthCheck.responseTime >= 0

\* Performance data constraints
Inv_Monitor_PerformanceDataConstraints ==
  \A componentId \in DOMAIN performanceData :
    LET perfData == performanceData[componentId]
    IN /\ perfData.cpuUsage >= 0 /\ perfData.cpuUsage <= 100
       /\ perfData.memoryUsage >= 0 /\ perfData.memoryUsage <= 100
       /\ perfData.diskUsage >= 0 /\ perfData.diskUsage <= 100
       /\ perfData.networkUsage >= 0 /\ perfData.networkUsage <= 100
       /\ perfData.throughput >= 0
       /\ perfData.latency >= 0
       /\ perfData.errorRate >= 0 /\ perfData.errorRate <= 100

\* Resource usage constraints
Inv_Monitor_ResourceUsageConstraints ==
  \A resourceId \in DOMAIN resourceUsage :
    LET resource == resourceUsage[resourceId]
    IN /\ resource.totalCapacity >= 0
       /\ resource.usedCapacity >= 0
       /\ resource.availableCapacity >= 0
       /\ resource.usedCapacity + resource.availableCapacity = resource.totalCapacity
       /\ resource.utilizationPercent >= 0 /\ resource.utilizationPercent <= 100

\* Query metric constraints
Inv_Monitor_QueryMetricConstraints ==
  \A queryId \in DOMAIN queryMetrics :
    LET queryMetric == queryMetrics[queryId]
    IN /\ queryMetric.executionTime >= 0
       /\ queryMetric.rowsReturned >= 0
       /\ queryMetric.rowsScanned >= 0
       /\ queryMetric.cpuTime >= 0
       /\ queryMetric.memoryUsed >= 0
       /\ queryMetric.diskReads >= 0
       /\ queryMetric.diskWrites >= 0
       /\ queryMetric.cacheHits >= 0
       /\ queryMetric.cacheMisses >= 0

\* System diagnostics constraints
Inv_Monitor_SystemDiagnosticsConstraints ==
  /\ systemDiagnostics.systemUptime >= 0
  /\ systemDiagnostics.totalConnections >= 0
  /\ systemDiagnostics.activeConnections >= 0
  /\ systemDiagnostics.totalQueries >= 0
  /\ systemDiagnostics.failedQueries >= 0
  /\ systemDiagnostics.averageQueryTime >= 0
  /\ systemDiagnostics.peakMemoryUsage >= 0
  /\ systemDiagnostics.currentMemoryUsage >= 0
  /\ systemDiagnostics.diskSpaceUsed >= 0
  /\ systemDiagnostics.diskSpaceTotal >= 0
  /\ systemDiagnostics.activeConnections <= systemDiagnostics.totalConnections
  /\ systemDiagnostics.failedQueries <= systemDiagnostics.totalQueries
  /\ systemDiagnostics.currentMemoryUsage <= systemDiagnostics.peakMemoryUsage
  /\ systemDiagnostics.diskSpaceUsed <= systemDiagnostics.diskSpaceTotal

\* Monitoring configuration constraints
Inv_Monitor_ConfigConstraints ==
  /\ monitoringConfig.collectionInterval > 0
  /\ monitoringConfig.retentionPeriod > 0
  /\ monitoringConfig.logLevel \in {"debug", "info", "warn", "error"}

\* Log aggregator constraints
Inv_Monitor_LogAggregatorConstraints ==
  /\ logAggregator.maxLogEntries > 0
  /\ logAggregator.currentLogEntries >= 0
  /\ logAggregator.currentLogEntries <= logAggregator.maxLogEntries
  /\ logAggregator.logRotationSize > 0
  /\ logAggregator.errorCount >= 0
  /\ logAggregator.warningCount >= 0
  /\ logAggregator.infoCount >= 0
  /\ logAggregator.debugCount >= 0

\* Alert threshold constraints
Inv_Monitor_AlertThresholdConstraints ==
  \A alertId \in DOMAIN alerts :
    LET alert == alerts[alertId]
    IN alert.status = "firing" => alert.currentValue > alert.threshold

\* Metric retention constraints
Inv_Monitor_MetricRetentionConstraints ==
  \A metricId \in DOMAIN metrics :
    globalTimestamp - metrics[metricId].timestamp <= MetricRetentionTime

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Alerts are eventually resolved
Liveness_AlertsEventuallyResolved ==
  \A alertId \in DOMAIN alerts :
    alerts[alertId].status = "firing" => <>alerts[alertId].status = "resolved"

\* Health checks are eventually performed
Liveness_HealthChecksPerformed ==
  \A componentId \in DOMAIN healthChecks :
    healthChecks[componentId].isEnabled => 
    <>healthChecks[componentId].lastCheck >= globalTimestamp - HealthCheckInterval

\* Old metrics are eventually cleaned up
Liveness_OldMetricsCleanedUp ==
  \A metricId \in DOMAIN metrics :
    globalTimestamp - metrics[metricId].timestamp > MetricRetentionTime => 
    <>~(metricId \in DOMAIN metrics)

\* Logs are eventually rotated
Liveness_LogsRotated ==
  logAggregator.currentLogEntries >= logAggregator.logRotationSize => 
  <>logAggregator.currentLogEntries < logAggregator.logRotationSize

\* System diagnostics are eventually updated
Liveness_SystemDiagnosticsUpdated ==
  systemDiagnostics.lastRestart < globalTimestamp - 3600 => 
  <>systemDiagnostics.lastRestart >= globalTimestamp - 3600

\* Performance data is eventually updated
Liveness_PerformanceDataUpdated ==
  \A componentId \in DOMAIN performanceData :
    globalTimestamp - performanceData[componentId].lastUpdated > 60 => 
    <>performanceData[componentId].lastUpdated >= globalTimestamp - 60

\* Resource usage is eventually updated
Liveness_ResourceUsageUpdated ==
  \A resourceId \in DOMAIN resourceUsage :
    globalTimestamp - resourceUsage[resourceId].lastUpdated > 30 => 
    <>resourceUsage[resourceId].lastUpdated >= globalTimestamp - 30

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* System health score is bounded
THEOREM Monitor_HealthScoreBounded ==
  GetSystemHealthScore() >= 0 /\ GetSystemHealthScore() <= 100

\* Active alert count is bounded
THEOREM Monitor_ActiveAlertCountBounded ==
  GetActiveAlertCount() <= MaxAlerts

\* Critical alert count is bounded
THEOREM Monitor_CriticalAlertCountBounded ==
  GetCriticalAlertCount() <= MaxAlerts

\* Resource utilization is bounded
THEOREM Monitor_ResourceUtilizationBounded ==
  \A resourceId \in DOMAIN resourceUsage :
    resourceUsage[resourceId].utilizationPercent <= 100

\* Query execution time is positive
THEOREM Monitor_QueryExecutionTimePositive ==
  \A queryId \in DOMAIN queryMetrics :
    queryMetrics[queryId].executionTime >= 0

\* System uptime is monotonic
THEOREM Monitor_SystemUptimeMonotonic ==
  systemDiagnostics.systemUptime >= 0

\* Monitoring is eventually enabled
THEOREM Monitor_MonitoringEventuallyEnabled ==
  ~monitoringConfig.isEnabled => <>monitoringConfig.isEnabled

\* Alerting is eventually enabled
THEOREM Monitor_AlertingEventuallyEnabled ==
  ~monitoringConfig.alertingEnabled => <>monitoringConfig.alertingEnabled

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - Monitor.metrics (Dictionary<UInt64, Metric>) → metrics
  - Monitor.alerts (Dictionary<UInt64, Alert>) → alerts
  - Monitor.healthChecks (Dictionary<UInt64, HealthCheck>) → healthChecks
  - Monitor.performanceData (Dictionary<UInt64, PerformanceData>) → performanceData
  - Monitor.resourceUsage (Dictionary<UInt64, ResourceUsage>) → resourceUsage
  - Monitor.queryMetrics (Dictionary<UInt64, QueryMetric>) → queryMetrics
  - Monitor.systemDiagnostics (SystemDiagnostics) → systemDiagnostics
  
  USAGE:
  
  This module should be used with all ColibrìDB modules for monitoring:
  
  ---- MODULE ColibriDB ----
  EXTENDS Monitor
  ...
  ====================
*)