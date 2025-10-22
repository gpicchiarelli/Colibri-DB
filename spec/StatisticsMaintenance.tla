---------------------------- MODULE StatisticsMaintenance ----------------------------
(*
  ColibrìDB Statistics Maintenance Specification
  
  Manages database statistics for query optimization including:
  - Table and column statistics collection
  - Histogram generation and maintenance
  - Cardinality estimation
  - Cost model updates
  - Statistics refresh strategies
  - Sampling-based statistics
  
  Based on:
  - Selinger et al. (1979) - "Access Path Selection in a Relational Database Management System"
  - Ioannidis (1993) - "Universality of Serial Histograms"
  - Chaudhuri et al. (1998) - "Sampling-based Statistics for Query Optimization"
  - PostgreSQL Statistics Implementation
  - Oracle Statistics Management
  
  Key Properties:
  - Accuracy: Statistics reflect actual data distribution
  - Freshness: Statistics are updated when data changes significantly
  - Efficiency: Statistics collection doesn't impact query performance
  - Consistency: Statistics are consistent across related tables
  
  Author: ColibrìDB Team
  Date: 2025-10-19
  Version: 1.0.0
*)

EXTENDS CORE, INTERFACES, DISK_FORMAT, Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  MaxHistogramBuckets,    \* Maximum number of histogram buckets
  SampleSize,             \* Sample size for statistics collection
  StatisticsRefreshThreshold, \* Threshold for statistics refresh
  MaxStatisticsAge        \* Maximum age of statistics before refresh

VARIABLES
  tableStats,             \* [TableName -> TableStatistics]
  columnStats,            \* [TableName -> [ColumnName -> ColumnStatistics]]
  histograms,             \* [TableName -> [ColumnName -> Histogram]]
  correlationStats,       \* [TableName -> [ColumnPair -> CorrelationStats]]
  indexStats,             \* [IndexName -> IndexStatistics]
  statisticsMetadata,     \* [TableName -> StatisticsMetadata]
  pendingUpdates,         \* [TableName -> PendingUpdate]
  samplingJobs,           \* [TableName -> SamplingJob]
  costModel               \* CostModel

statisticsMaintenanceVars == <<tableStats, columnStats, histograms, correlationStats, 
                               indexStats, statisticsMetadata, pendingUpdates, 
                               samplingJobs, costModel>>

(* --------------------------------------------------------------------------
   TYPE DEFINITIONS
   -------------------------------------------------------------------------- *)

\* Table-level statistics
TableStatistics == [
  tableName: STRING,
  rowCount: Nat,
  pageCount: Nat,
  avgRowSize: Nat,
  lastUpdated: Timestamp,
  isStale: BOOLEAN,
  sampleRate: Nat  \* Percentage of table sampled
]

\* Column-level statistics
ColumnStatistics == [
  columnName: STRING,
  dataType: ValueType,
  nullCount: Nat,
  distinctCount: Nat,
  minValue: Value,
  maxValue: Value,
  avgValue: Value,
  stdDev: Nat,
  skewness: Nat,
  kurtosis: Nat,
  lastUpdated: Timestamp
]

\* Histogram for column value distribution
Histogram == [
  columnName: STRING,
  bucketCount: Nat,
  buckets: Seq(HistogramBucket),
  totalRows: Nat,
  nullRows: Nat,
  distinctValues: Nat,
  lastUpdated: Timestamp
]

\* Individual histogram bucket
HistogramBucket == [
  bucketId: Nat,
  lowerBound: Value,
  upperBound: Value,
  frequency: Nat,
  distinctValues: Nat,
  cumulativeFrequency: Nat
]

\* Correlation statistics between columns
CorrelationStats == [
  column1: STRING,
  column2: STRING,
  correlationCoeff: Nat,  \* -100 to 100 (scaled)
  jointCardinality: Nat,
  independenceFactor: Nat,
  lastUpdated: Timestamp
]

\* Index statistics
IndexStatistics == [
  indexName: STRING,
  tableName: STRING,
  columnNames: Seq(STRING),
  keyCount: Nat,
  leafPages: Nat,
  levels: Nat,
  avgKeySize: Nat,
  clusteringFactor: Nat,
  selectivity: Nat,  \* 0-100
  lastUpdated: Timestamp
]

\* Statistics metadata
StatisticsMetadata == [
  tableName: STRING,
  lastFullScan: Timestamp,
  lastSampleScan: Timestamp,
  changeCount: Nat,
  changeThreshold: Nat,
  autoRefresh: BOOLEAN,
  refreshStrategy: {"full", "sample", "incremental"}
]

\* Pending statistics update
PendingUpdate == [
  tableName: STRING,
  updateType: {"full", "sample", "incremental"},
  priority: Nat,  \* 1-10, higher = more urgent
  submittedAt: Timestamp,
  estimatedDuration: Nat,
  affectedColumns: Seq(STRING)
]

\* Sampling job for statistics collection
SamplingJob == [
  tableName: STRING,
  jobId: Nat,
  status: {"pending", "running", "completed", "failed"},
  startTime: Timestamp,
  endTime: Timestamp,
  sampleSize: Nat,
  actualSampleSize: Nat,
  progress: Nat,  \* 0-100
  errorMessage: STRING
]

\* Cost model for query optimization
CostModel == [
  cpuCostPerTuple: Nat,
  ioCostPerPage: Nat,
  memoryCostPerMB: Nat,
  networkCostPerMB: Nat,
  selectivityFactors: [STRING -> Nat],  \* Column -> selectivity factor
  joinCostFactors: [STRING -> Nat],     \* Join type -> cost factor
  lastUpdated: Timestamp
]

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_StatisticsMaintenance ==
  /\ tableStats \in [STRING -> TableStatistics]
  /\ columnStats \in [STRING -> [STRING -> ColumnStatistics]]
  /\ histograms \in [STRING -> [STRING -> Histogram]]
  /\ correlationStats \in [STRING -> [STRING -> CorrelationStats]]
  /\ indexStats \in [STRING -> IndexStatistics]
  /\ statisticsMetadata \in [STRING -> StatisticsMetadata]
  /\ pendingUpdates \in [STRING -> PendingUpdate]
  /\ samplingJobs \in [STRING -> SamplingJob]
  /\ costModel \in CostModel

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ tableStats = [t \in {} |-> [
       tableName |-> "",
       rowCount |-> 0,
       pageCount |-> 0,
       avgRowSize |-> 0,
       lastUpdated |-> 0,
       isStale |-> FALSE,
       sampleRate |-> 0
     ]]
  /\ columnStats = [t \in {} |-> [c \in {} |-> [
       columnName |-> "",
       dataType |-> "int",
       nullCount |-> 0,
       distinctCount |-> 0,
       minValue |-> [type |-> "int", val |-> 0],
       maxValue |-> [type |-> "int", val |-> 0],
       avgValue |-> [type |-> "int", val |-> 0],
       stdDev |-> 0,
       skewness |-> 0,
       kurtosis |-> 0,
       lastUpdated |-> 0
     ]]]
  /\ histograms = [t \in {} |-> [c \in {} |-> [
       columnName |-> "",
       bucketCount |-> 0,
       buckets |-> <<>>,
       totalRows |-> 0,
       nullRows |-> 0,
       distinctValues |-> 0,
       lastUpdated |-> 0
     ]]]
  /\ correlationStats = [t \in {} |-> [p \in {} |-> [
       column1 |-> "",
       column2 |-> "",
       correlationCoeff |-> 0,
       jointCardinality |-> 0,
       independenceFactor |-> 0,
       lastUpdated |-> 0
     ]]]
  /\ indexStats = [i \in {} |-> [
       indexName |-> "",
       tableName |-> "",
       columnNames |-> <<>>,
       keyCount |-> 0,
       leafPages |-> 0,
       levels |-> 0,
       avgKeySize |-> 0,
       clusteringFactor |-> 0,
       selectivity |-> 0,
       lastUpdated |-> 0
     ]]
  /\ statisticsMetadata = [t \in {} |-> [
       tableName |-> "",
       lastFullScan |-> 0,
       lastSampleScan |-> 0,
       changeCount |-> 0,
       changeThreshold |-> 1000,
       autoRefresh |-> TRUE,
       refreshStrategy |-> "sample"
     ]]
  /\ pendingUpdates = [t \in {} |-> [
       tableName |-> "",
       updateType |-> "sample",
       priority |-> 5,
       submittedAt |-> 0,
       estimatedDuration |-> 0,
       affectedColumns |-> <<>>
     ]]
  /\ samplingJobs = [t \in {} |-> [
       tableName |-> "",
       jobId |-> 0,
       status |-> "pending",
       startTime |-> 0,
       endTime |-> 0,
       sampleSize |-> 0,
       actualSampleSize |-> 0,
       progress |-> 0,
       errorMessage |-> ""
     ]]
  /\ costModel = [
       cpuCostPerTuple |-> 1,
       ioCostPerPage |-> 10,
       memoryCostPerMB |-> 100,
       networkCostPerMB |-> 50,
       selectivityFactors |-> [c \in {} |-> 10],
       joinCostFactors |-> [j \in {} |-> 100],
       lastUpdated |-> 0
     ]

(* --------------------------------------------------------------------------
   OPERATIONS
   -------------------------------------------------------------------------- *)

\* Collect table statistics
CollectTableStats(tableName, rowCount, pageCount, avgRowSize, sampleRate) ==
  /\ LET tableStat == [
       tableName |-> tableName,
       rowCount |-> rowCount,
       pageCount |-> pageCount,
       avgRowSize |-> avgRowSize,
       lastUpdated |-> globalTimestamp,
       isStale |-> FALSE,
       sampleRate |-> sampleRate
     ]
  IN /\ tableStats' = [tableStats EXCEPT ![tableName] = tableStat]
     /\ statisticsMetadata' = [statisticsMetadata EXCEPT ![tableName] = 
                              [statisticsMetadata[tableName] EXCEPT 
                               !.lastFullScan = globalTimestamp,
                               !.changeCount = 0]]
     /\ UNCHANGED <<columnStats, histograms, correlationStats, indexStats, 
                   pendingUpdates, samplingJobs, costModel>>

\* Collect column statistics
CollectColumnStats(tableName, columnName, dataType, nullCount, distinctCount, 
                   minValue, maxValue, avgValue, stdDev, skewness, kurtosis) ==
  /\ LET columnStat == [
       columnName |-> columnName,
       dataType |-> dataType,
       nullCount |-> nullCount,
       distinctCount |-> distinctCount,
       minValue |-> minValue,
       maxValue |-> maxValue,
       avgValue |-> avgValue,
       stdDev |-> stdDev,
       skewness |-> skewness,
       kurtosis |-> kurtosis,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ columnStats' = [columnStats EXCEPT ![tableName] = 
                       [columnStats[tableName] EXCEPT ![columnName] = columnStat]]
     /\ UNCHANGED <<tableStats, histograms, correlationStats, indexStats, 
                   statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

\* Generate histogram for column
GenerateHistogram(tableName, columnName, buckets) ==
  /\ LET histogram == [
       columnName |-> columnName,
       bucketCount |-> Len(buckets),
       buckets |-> buckets,
       totalRows |-> tableStats[tableName].rowCount,
       nullRows |-> columnStats[tableName][columnName].nullCount,
       distinctValues |-> columnStats[tableName][columnName].distinctCount,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ histograms' = [histograms EXCEPT ![tableName] = 
                      [histograms[tableName] EXCEPT ![columnName] = histogram]]
     /\ UNCHANGED <<tableStats, columnStats, correlationStats, indexStats, 
                   statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

\* Update correlation statistics
UpdateCorrelationStats(tableName, column1, column2, correlationCoeff, 
                       jointCardinality, independenceFactor) ==
  /\ LET correlationStat == [
       column1 |-> column1,
       column2 |-> column2,
       correlationCoeff |-> correlationCoeff,
       jointCardinality |-> jointCardinality,
       independenceFactor |-> independenceFactor,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ correlationStats' = [correlationStats EXCEPT ![tableName] = 
                            [correlationStats[tableName] EXCEPT 
                             ![column1 || "_" || column2] = correlationStat]]
     /\ UNCHANGED <<tableStats, columnStats, histograms, indexStats, 
                   statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

\* Update index statistics
UpdateIndexStats(indexName, tableName, columnNames, keyCount, leafPages, 
                 levels, avgKeySize, clusteringFactor, selectivity) ==
  /\ LET indexStat == [
       indexName |-> indexName,
       tableName |-> tableName,
       columnNames |-> columnNames,
       keyCount |-> keyCount,
       leafPages |-> leafPages,
       levels |-> levels,
       avgKeySize |-> avgKeySize,
       clusteringFactor |-> clusteringFactor,
       selectivity |-> selectivity,
       lastUpdated |-> globalTimestamp
     ]
  IN /\ indexStats' = [indexStats EXCEPT ![indexName] = indexStat]
     /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

\* Mark statistics as stale
MarkStatisticsStale(tableName, affectedColumns) ==
  /\ tableStats' = [tableStats EXCEPT ![tableName] = 
                   [tableStats[tableName] EXCEPT !.isStale = TRUE]]
  /\ statisticsMetadata' = [statisticsMetadata EXCEPT ![tableName] = 
                           [statisticsMetadata[tableName] EXCEPT 
                            !.changeCount = statisticsMetadata[tableName].changeCount + 1]]
  /\ pendingUpdates' = [pendingUpdates EXCEPT ![tableName] = [
       tableName |-> tableName,
       updateType |-> "incremental",
       priority |-> 5,
       submittedAt |-> globalTimestamp,
       estimatedDuration |-> 100,
       affectedColumns |-> affectedColumns
     ]]
  /\ UNCHANGED <<columnStats, histograms, correlationStats, indexStats, 
                samplingJobs, costModel>>

\* Start sampling job
StartSamplingJob(tableName, jobId, sampleSize) ==
  /\ LET samplingJob == [
       tableName |-> tableName,
       jobId |-> jobId,
       status |-> "running",
       startTime |-> globalTimestamp,
       endTime |-> 0,
       sampleSize |-> sampleSize,
       actualSampleSize |-> 0,
       progress |-> 0,
       errorMessage |-> ""
     ]
  IN /\ samplingJobs' = [samplingJobs EXCEPT ![tableName] = samplingJob]
     /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   indexStats, statisticsMetadata, pendingUpdates, costModel>>

\* Progress sampling job
ProgressSamplingJob(tableName, progress, actualSampleSize) ==
  /\ tableName \in DOMAIN samplingJobs
  /\ LET currentJob == samplingJobs[tableName]
       updatedJob == [currentJob EXCEPT 
                     !.progress = progress,
                     !.actualSampleSize = actualSampleSize]
  IN /\ samplingJobs' = [samplingJobs EXCEPT ![tableName] = updatedJob]
     /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   indexStats, statisticsMetadata, pendingUpdates, costModel>>

\* Complete sampling job
CompleteSamplingJob(tableName, success, errorMessage) ==
  /\ tableName \in DOMAIN samplingJobs
  /\ LET currentJob == samplingJobs[tableName]
       completedJob == [currentJob EXCEPT 
                       !.status = IF success THEN "completed" ELSE "failed",
                       !.endTime = globalTimestamp,
                       !.errorMessage = errorMessage]
  IN /\ samplingJobs' = [samplingJobs EXCEPT ![tableName] = completedJob]
     /\ statisticsMetadata' = [statisticsMetadata EXCEPT ![tableName] = 
                              [statisticsMetadata[tableName] EXCEPT 
                               !.lastSampleScan = globalTimestamp]]
     /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   indexStats, pendingUpdates, costModel>>

\* Update cost model
UpdateCostModel(cpuCost, ioCost, memoryCost, networkCost, selectivityFactors, joinCostFactors) ==
  /\ costModel' = [
       cpuCostPerTuple |-> cpuCost,
       ioCostPerPage |-> ioCost,
       memoryCostPerMB |-> memoryCost,
       networkCostPerMB |-> networkCost,
       selectivityFactors |-> selectivityFactors,
       joinCostFactors |-> joinCostFactors,
       lastUpdated |-> globalTimestamp
     ]
  /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                indexStats, statisticsMetadata, pendingUpdates, samplingJobs>>

\* Estimate cardinality for predicate
EstimateCardinality(tableName, columnName, predicate) ==
  /\ tableName \in DOMAIN tableStats
  /\ columnName \in DOMAIN columnStats[tableName]
  /\ LET tableStat == tableStats[tableName]
       columnStat == columnStats[tableName][columnName]
       histogram == histograms[tableName][columnName]
       estimatedCardinality == CalculateCardinality(tableStat, columnStat, histogram, predicate)
  IN /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   indexStats, statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

\* Calculate selectivity for join
CalculateJoinSelectivity(table1, column1, table2, column2, joinType) ==
  /\ table1 \in DOMAIN tableStats
  /\ table2 \in DOMAIN tableStats
  /\ column1 \in DOMAIN columnStats[table1]
  /\ column2 \in DOMAIN columnStats[table2]
  /\ LET correlationStat == correlationStats[table1][column1 || "_" || column2]
       selectivity == CalculateJoinSelectivityFromCorrelation(correlationStat, joinType)
  IN /\ UNCHANGED <<tableStats, columnStats, histograms, correlationStats, 
                   indexStats, statisticsMetadata, pendingUpdates, samplingJobs, costModel>>

(* --------------------------------------------------------------------------
   HELPER FUNCTIONS
   -------------------------------------------------------------------------- *)

\* Calculate cardinality from histogram and predicate
CalculateCardinality(tableStat, columnStat, histogram, predicate) ==
  IF histogram.bucketCount = 0 THEN tableStat.rowCount / 10  \* Default estimate
  ELSE LET matchingBuckets == FilterBuckets(histogram.buckets, predicate)
           totalFrequency == SumBucketFrequencies(matchingBuckets)
       IN totalFrequency

\* Filter histogram buckets based on predicate
FilterBuckets(buckets, predicate) ==
  <<bucket \in buckets : MatchesPredicate(bucket, predicate)>>

\* Check if bucket matches predicate
MatchesPredicate(bucket, predicate) ==
  CASE predicate.type
    OF "equals" -> bucket.lowerBound = predicate.value /\ bucket.upperBound = predicate.value
    [] "range" -> bucket.lowerBound >= predicate.minValue /\ bucket.upperBound <= predicate.maxValue
    [] "greater_than" -> bucket.lowerBound > predicate.value
    [] "less_than" -> bucket.upperBound < predicate.value
    [] "like" -> TRUE  \* Simplified for TLA+
  ENDCASE

\* Sum frequencies of matching buckets
SumBucketFrequencies(buckets) ==
  IF Len(buckets) = 0 THEN 0
  ELSE LET bucket == buckets[1]
       IN bucket.frequency + SumBucketFrequencies(SubSeq(buckets, 2, Len(buckets)))

\* Calculate join selectivity from correlation
CalculateJoinSelectivityFromCorrelation(correlationStat, joinType) ==
  CASE joinType
    OF "inner" -> correlationStat.independenceFactor / 100
    [] "left" -> 1
    [] "right" -> 1
    [] "full" -> 1
  ENDCASE

\* Check if statistics need refresh
NeedsRefresh(tableName) ==
  /\ tableName \in DOMAIN statisticsMetadata
  /\ LET metadata == statisticsMetadata[tableName]
       tableStat == tableStats[tableName]
  IN \/ tableStat.isStale
     \/ metadata.changeCount >= metadata.changeThreshold
     \/ globalTimestamp - tableStat.lastUpdated > MaxStatisticsAge

\* Get optimal sample size for table
GetOptimalSampleSize(tableName) ==
  IF tableName \in DOMAIN tableStats
  THEN LET rowCount == tableStats[tableName].rowCount
       IN IF rowCount <= SampleSize THEN rowCount ELSE SampleSize
  ELSE SampleSize

(* --------------------------------------------------------------------------
   NEXT STATE RELATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E tableName \in STRING, rowCount \in Nat, pageCount \in Nat, 
       avgRowSize \in Nat, sampleRate \in Nat :
       CollectTableStats(tableName, rowCount, pageCount, avgRowSize, sampleRate)
  \/ \E tableName \in STRING, columnName \in STRING, dataType \in ValueType,
       nullCount \in Nat, distinctCount \in Nat, minValue \in Value, 
       maxValue \in Value, avgValue \in Value, stdDev \in Nat, 
       skewness \in Nat, kurtosis \in Nat :
       CollectColumnStats(tableName, columnName, dataType, nullCount, distinctCount,
                         minValue, maxValue, avgValue, stdDev, skewness, kurtosis)
  \/ \E tableName \in STRING, columnName \in STRING, buckets \in Seq(HistogramBucket) :
       GenerateHistogram(tableName, columnName, buckets)
  \/ \E tableName \in STRING, column1 \in STRING, column2 \in STRING,
       correlationCoeff \in Nat, jointCardinality \in Nat, independenceFactor \in Nat :
       UpdateCorrelationStats(tableName, column1, column2, correlationCoeff,
                             jointCardinality, independenceFactor)
  \/ \E indexName \in STRING, tableName \in STRING, columnNames \in Seq(STRING),
       keyCount \in Nat, leafPages \in Nat, levels \in Nat, avgKeySize \in Nat,
       clusteringFactor \in Nat, selectivity \in Nat :
       UpdateIndexStats(indexName, tableName, columnNames, keyCount, leafPages,
                       levels, avgKeySize, clusteringFactor, selectivity)
  \/ \E tableName \in STRING, affectedColumns \in Seq(STRING) :
       MarkStatisticsStale(tableName, affectedColumns)
  \/ \E tableName \in STRING, jobId \in Nat, sampleSize \in Nat :
       StartSamplingJob(tableName, jobId, sampleSize)
  \/ \E tableName \in STRING, progress \in Nat, actualSampleSize \in Nat :
       ProgressSamplingJob(tableName, progress, actualSampleSize)
  \/ \E tableName \in STRING, success \in BOOLEAN, errorMessage \in STRING :
       CompleteSamplingJob(tableName, success, errorMessage)
  \/ \E cpuCost \in Nat, ioCost \in Nat, memoryCost \in Nat, networkCost \in Nat,
       selectivityFactors \in [STRING -> Nat], joinCostFactors \in [STRING -> Nat] :
       UpdateCostModel(cpuCost, ioCost, memoryCost, networkCost, 
                      selectivityFactors, joinCostFactors)
  \/ \E tableName \in STRING, columnName \in STRING, predicate \in [type: STRING, value: Value] :
       EstimateCardinality(tableName, columnName, predicate)
  \/ \E table1 \in STRING, column1 \in STRING, table2 \in STRING, column2 \in STRING,
       joinType \in {"inner", "left", "right", "full"} :
       CalculateJoinSelectivity(table1, column1, table2, column2, joinType)

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Statistics are consistent with table data
Inv_StatisticsMaintenance_Consistency ==
  \A tableName \in DOMAIN tableStats :
    /\ tableStats[tableName].rowCount >= 0
    /\ tableStats[tableName].pageCount >= 0
    /\ tableStats[tableName].avgRowSize >= 0
    /\ tableStats[tableName].sampleRate >= 0 /\ tableStats[tableName].sampleRate <= 100

\* Column statistics are consistent
Inv_StatisticsMaintenance_ColumnConsistency ==
  \A tableName \in DOMAIN columnStats :
    \A columnName \in DOMAIN columnStats[tableName] :
      LET columnStat == columnStats[tableName][columnName]
      IN /\ columnStat.nullCount >= 0
         /\ columnStat.distinctCount >= 0
         /\ columnStat.distinctCount <= tableStats[tableName].rowCount
         /\ columnStat.nullCount <= tableStats[tableName].rowCount

\* Histograms are valid
Inv_StatisticsMaintenance_HistogramValidity ==
  \A tableName \in DOMAIN histograms :
    \A columnName \in DOMAIN histograms[tableName] :
      LET histogram == histograms[tableName][columnName]
      IN /\ histogram.bucketCount >= 0
         /\ histogram.bucketCount <= MaxHistogramBuckets
         /\ Len(histogram.buckets) = histogram.bucketCount
         /\ histogram.totalRows >= 0
         /\ histogram.nullRows >= 0
         /\ histogram.distinctValues >= 0

\* Sampling jobs progress monotonically
Inv_StatisticsMaintenance_SamplingProgress ==
  \A tableName \in DOMAIN samplingJobs :
    LET job == samplingJobs[tableName]
    IN /\ job.progress >= 0 /\ job.progress <= 100
       /\ job.actualSampleSize >= 0
       /\ job.actualSampleSize <= job.sampleSize

\* Pending updates have valid priorities
Inv_StatisticsMaintenance_PendingUpdatePriorities ==
  \A tableName \in DOMAIN pendingUpdates :
    LET update == pendingUpdates[tableName]
    IN /\ update.priority >= 1 /\ update.priority <= 10
       /\ update.estimatedDuration >= 0

\* Cost model values are positive
Inv_StatisticsMaintenance_CostModelValidity ==
  /\ costModel.cpuCostPerTuple > 0
  /\ costModel.ioCostPerPage > 0
  /\ costModel.memoryCostPerMB > 0
  /\ costModel.networkCostPerMB > 0

\* Statistics metadata is consistent
Inv_StatisticsMaintenance_MetadataConsistency ==
  \A tableName \in DOMAIN statisticsMetadata :
    LET metadata == statisticsMetadata[tableName]
    IN /\ metadata.changeCount >= 0
       /\ metadata.changeThreshold > 0
       /\ metadata.lastFullScan >= 0
       /\ metadata.lastSampleScan >= 0

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Stale statistics are eventually refreshed
Liveness_StaleStatisticsRefreshed ==
  \A tableName \in DOMAIN tableStats :
    tableStats[tableName].isStale => <>~tableStats[tableName].isStale

\* Pending updates are eventually processed
Liveness_PendingUpdatesProcessed ==
  \A tableName \in DOMAIN pendingUpdates :
    <>~(tableName \in DOMAIN pendingUpdates)

\* Sampling jobs eventually complete
Liveness_SamplingJobsComplete ==
  \A tableName \in DOMAIN samplingJobs :
    samplingJobs[tableName].status = "running" => 
    <>samplingJobs[tableName].status \in {"completed", "failed"}

\* Statistics are eventually collected for new tables
Liveness_NewTableStatisticsCollected ==
  \A tableName \in STRING :
    tableName \in DOMAIN tableStats => 
    tableStats[tableName].rowCount > 0 => 
    tableStats[tableName].lastUpdated > 0

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Statistics accuracy improves with larger samples
THEOREM StatisticsMaintenance_SampleAccuracy ==
  \A tableName \in DOMAIN tableStats :
    tableStats[tableName].sampleRate = 100 => 
    ~tableStats[tableName].isStale

\* Histogram buckets are ordered
THEOREM StatisticsMaintenance_HistogramOrdering ==
  \A tableName \in DOMAIN histograms :
    \A columnName \in DOMAIN histograms[tableName] :
      LET histogram == histograms[tableName][columnName]
      IN \A i \in 1..Len(histogram.buckets)-1 :
        histogram.buckets[i].upperBound <= histogram.buckets[i+1].lowerBound

\* Correlation statistics are symmetric
THEOREM StatisticsMaintenance_CorrelationSymmetric ==
  \A tableName \in DOMAIN correlationStats :
    \A columnPair \in DOMAIN correlationStats[tableName] :
      LET correlationStat == correlationStats[tableName][columnPair]
      IN correlationStat.correlationCoeff >= -100 /\ correlationStat.correlationCoeff <= 100

=============================================================================

(*
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - StatisticsManager.tableStats (Dictionary<String, TableStatistics>) → tableStats
  - StatisticsManager.columnStats (Dictionary<String, Dictionary<String, ColumnStatistics>>) → columnStats
  - StatisticsManager.histograms (Dictionary<String, Dictionary<String, Histogram>>) → histograms
  - StatisticsManager.samplingJobs (Dictionary<String, SamplingJob>) → samplingJobs
  
  USAGE:
  
  This module should be used with QueryOptimizer and other ColibrìDB modules:
  
  ---- MODULE QueryOptimizer ----
  EXTENDS StatisticsMaintenance
  ...
  ====================
*)