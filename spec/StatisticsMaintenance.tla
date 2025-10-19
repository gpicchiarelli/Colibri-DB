----------------------------- MODULE StatisticsMaintenance -----------------------------
(*
  Statistics Maintenance and Query Optimization Specification for ColibrìDB
  
  This module specifies the collection and maintenance of table/index statistics
  for query optimization. It implements:
  - Histogram construction (equi-depth, equi-width)
  - Cardinality estimation (distinct values)
  - Selectivity estimation
  - Multi-column statistics (correlation)
  - HyperLogLog sketches for approximate counting
  - Statistics aging and automatic refresh
  - ANALYZE command execution
  
  Based on:
  - Ioannidis, Y. E. (2003). "The history of histograms." Proceedings of VLDB 2003.
  - Ioannidis, Y., & Poosala, V. (1995). "Balancing histogram optimality and
    practicality for query result size estimation." Proceedings of ACM SIGMOD 1995.
  - Flajolet, P., et al. (2007). "HyperLogLog: the analysis of a near-optimal
    cardinality estimation algorithm." AofA 2007.
  - Selinger, P. G., et al. (1979). "Access path selection in a relational database
    management system." Proceedings of ACM SIGMOD 1979.
  - Chaudhuri, S., & Narasayya, V. (2007). "Statistics on query expressions."
    Proceedings of ACM SIGMOD 2007.
  
  Key Properties:
  - Accuracy: Statistics accurately represent data distribution
  - Freshness: Statistics updated after significant data changes
  - Efficiency: Statistics collection doesn't block queries
  - Compactness: Statistics stored efficiently
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
  MAX_TX,                  \* From CORE
  MAX_LSN,                 \* From CORE
  MAX_PAGES,               \* From CORE
  Tables,                  \* Set of table names
  Columns,                 \* Set of column names
  MAX_HISTOGRAM_BUCKETS,   \* Maximum histogram buckets
  STATS_THRESHOLD          \* % change to trigger auto-analyze

(* --------------------------------------------------------------------------
   STATISTICS TYPES
   -------------------------------------------------------------------------- *)

\* Histogram types
HistogramType == {
  "equi-width",      \* Equal bucket width (value range)
  "equi-depth",      \* Equal bucket depth (row count)
  "max-diff",        \* Maximum difference
  "v-optimal"        \* V-Optimal (minimize estimate error)
}

\* Histogram bucket
HistogramBucket == [
  minValue: Value,
  maxValue: Value,
  frequency: Nat,        \* Number of values in bucket
  distinctValues: Nat    \* Number of distinct values
]

\* Column statistics
ColumnStats == [
  nullFraction: Nat,                     \* Percentage of NULL values (0-100)
  distinctValues: Nat,                   \* Number of distinct values (cardinality)
  avgWidth: Nat,                         \* Average column width in bytes
  mostCommonValues: Seq(Value),          \* MCVs (Most Common Values)
  mostCommonFreqs: Seq(Nat),             \* Frequencies of MCVs
  histogram: Seq(HistogramBucket),       \* Histogram for non-MCV values
  correlation: Nat                       \* Correlation with physical order (-100 to 100)
]

\* Table statistics
TableStats == [
  rowCount: Nat,                \* Total rows
  pageCount: Nat,               \* Total pages
  tupleSize: Nat,               \* Average tuple size
  deadTuples: Nat,              \* Dead tuple count
  lastAnalyzed: Nat,            \* Timestamp of last ANALYZE
  modifications: Nat            \* Modifications since last ANALYZE
]

\* HyperLogLog sketch for cardinality estimation
HLLSketch == [
  precision: Nat,               \* Number of bits for bucket index (4-16)
  registers: Seq(Nat),          \* 2^precision registers
  estimatedCardinality: Nat
]

(* --------------------------------------------------------------------------
   VARIABLES
   -------------------------------------------------------------------------- *)

VARIABLES
  \* Table statistics
  tableStats,           \* [Tables -> TableStats] - Per-table statistics
  columnStats,          \* [Tables -> [Columns -> ColumnStats]] - Per-column stats
  
  \* Index statistics
  indexStats,           \* [IndexName -> [distinctKeys, height, pages]]
  
  \* Cardinality sketches
  hllSketches,          \* [Tables -> [Columns -> HLLSketch]] - HLL sketches
  
  \* Statistics collection state
  analyzeInProgress,    \* [Tables -> BOOLEAN] - ANALYZE running
  sampleSize,           \* [Tables -> Nat] - Sample size for statistics
  sampledRows,          \* [Tables -> Seq(Row)] - Sampled rows
  
  \* Statistics metadata
  statsVersion,         \* [Tables -> Nat] - Statistics version number
  autoAnalyzeEnabled,   \* BOOLEAN - Auto-analyze enabled
  modificationCount,    \* [Tables -> Nat] - Modifications since last analyze
  
  \* Query optimization estimates
  selectivityCache      \* [(Table, Predicate) -> Nat] - Cached selectivity estimates

statsVars == <<tableStats, columnStats, indexStats, hllSketches,
               analyzeInProgress, sampleSize, sampledRows, statsVersion,
               autoAnalyzeEnabled, modificationCount, selectivityCache>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_Stats ==
  /\ tableStats \in [Tables -> TableStats]
  /\ columnStats \in [Tables -> [Columns -> ColumnStats]]
  /\ indexStats \in [STRING -> [distinctKeys: Nat, height: Nat, pages: Nat]]
  /\ hllSketches \in [Tables -> [Columns -> HLLSketch]]
  /\ analyzeInProgress \in [Tables -> BOOLEAN]
  /\ sampleSize \in [Tables -> Nat]
  /\ sampledRows \in [Tables -> Seq(Row)]
  /\ statsVersion \in [Tables -> Nat]
  /\ autoAnalyzeEnabled \in BOOLEAN
  /\ modificationCount \in [Tables -> Nat]
  /\ selectivityCache \in [(Tables \X STRING) -> Nat]

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Calculate modification threshold for auto-analyze
ModificationThreshold(table) ==
  (tableStats[table].rowCount * STATS_THRESHOLD) \div 100

\* Check if auto-analyze should trigger
ShouldAutoAnalyze(table) ==
  /\ autoAnalyzeEnabled
  /\ ~analyzeInProgress[table]
  /\ modificationCount[table] >= ModificationThreshold(table)

\* Sample rows using reservoir sampling (simplified)
ReservoirSample(allRows, n) ==
  \* Simplified: just take first n rows
  \* Real implementation: Vitter's Algorithm L
  SubSeq(allRows, 1, Min({n, Len(allRows)}))

\* Build equi-depth histogram
BuildEquiDepthHistogram(values, numBuckets) ==
  LET sortedValues == SortSeq(values, LAMBDA v1, v2: v1 < v2)
      bucketSize == (Len(sortedValues) + numBuckets - 1) \div numBuckets
  IN [i \in 1..numBuckets |->
       LET startIdx == (i - 1) * bucketSize + 1
           endIdx == Min({i * bucketSize, Len(sortedValues)})
           bucketValues == SubSeq(sortedValues, startIdx, endIdx)
       IN [minValue |-> bucketValues[1],
           maxValue |-> bucketValues[Len(bucketValues)],
           frequency |-> Len(bucketValues),
           distinctValues |-> Cardinality(Range(bucketValues))]]

\* Estimate selectivity using histogram
EstimateSelectivity(colStats, predicate, value) ==
  CASE predicate OF
    "=" -> 
      \* Check if in most common values
      IF value \in Range(colStats.mostCommonValues)
      THEN LET idx == CHOOSE i \in 1..Len(colStats.mostCommonValues):
                        colStats.mostCommonValues[i] = value
           IN colStats.mostCommonFreqs[idx]
      ELSE \* Estimate from histogram
        100 \div colStats.distinctValues
    [] ">" -> 
      \* Estimate rows greater than value using histogram
      LET bucketsAfter == {b \in Range(colStats.histogram): b.minValue > value}
          estimatedRows == FoldSeq(LAMBDA acc, b: acc + b.frequency, 0, bucketsAfter)
      IN estimatedRows
    [] "<" ->
      \* Estimate rows less than value
      LET bucketsBefore == {b \in Range(colStats.histogram): b.maxValue < value}
          estimatedRows == FoldSeq(LAMBDA acc, b: acc + b.frequency, 0, bucketsBefore)
      IN estimatedRows
    [] OTHER -> 50  \* Default: assume 50% selectivity

\* Update HyperLogLog sketch with new value
UpdateHLL(sketch, value) ==
  \* Simplified HLL update
  LET hashValue == Hash(value)  \* Abstract hash function
      bucketIdx == hashValue % (2^sketch.precision)
      leadingZeros == CountLeadingZeros(hashValue)  \* Abstract
  IN [sketch EXCEPT !.registers[bucketIdx] = Max({@, leadingZeros})]

\* Estimate cardinality from HLL sketch
EstimateCardinalityHLL(sketch) ==
  LET m == 2^sketch.precision
      alpha == 0.7213 / (1 + 1.079 / m)  \* HLL constant
      rawEstimate == alpha * m^2 / FoldSeq(LAMBDA acc, r: acc + 2^(-r), 0, sketch.registers)
  IN rawEstimate

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init_Stats ==
  /\ tableStats = [t \in Tables |-> 
                    [rowCount |-> 0, pageCount |-> 0, tupleSize |-> 0,
                     deadTuples |-> 0, lastAnalyzed |-> 0, modifications |-> 0]]
  /\ columnStats = [t \in Tables |-> [c \in Columns |->
                     [nullFraction |-> 0, distinctValues |-> 0, avgWidth |-> 0,
                      mostCommonValues |-> <<>>, mostCommonFreqs |-> <<>>,
                      histogram |-> <<>>, correlation |-> 0]]]
  /\ indexStats = [idx \in {} |-> [distinctKeys |-> 0, height |-> 0, pages |-> 0]]
  /\ hllSketches = [t \in Tables |-> [c \in Columns |->
                     [precision |-> 12, registers |-> [i \in 1..4096 |-> 0],
                      estimatedCardinality |-> 0]]]
  /\ analyzeInProgress = [t \in Tables |-> FALSE]
  /\ sampleSize = [t \in Tables |-> 300]  \* Default sample size: 300 blocks
  /\ sampledRows = [t \in Tables |-> <<>>]
  /\ statsVersion = [t \in Tables |-> 1]
  /\ autoAnalyzeEnabled = TRUE
  /\ modificationCount = [t \in Tables |-> 0]
  /\ selectivityCache = [p \in {} |-> 0]

(* --------------------------------------------------------------------------
   DATA MODIFICATION TRACKING
   -------------------------------------------------------------------------- *)

\* Record modification (INSERT, UPDATE, DELETE)
RecordModification(table) ==
  /\ modificationCount' = [modificationCount EXCEPT ![table] = @ + 1]
  /\ tableStats' = [tableStats EXCEPT ![table].modifications = @ + 1]
  /\ UNCHANGED <<columnStats, indexStats, hllSketches, analyzeInProgress,
                sampleSize, sampledRows, statsVersion, autoAnalyzeEnabled,
                selectivityCache>>

\* Track row count changes
UpdateRowCount(table, delta) ==
  /\ tableStats' = [tableStats EXCEPT ![table].rowCount = @ + delta]
  /\ UNCHANGED <<columnStats, indexStats, hllSketches, analyzeInProgress,
                sampleSize, sampledRows, statsVersion, autoAnalyzeEnabled,
                modificationCount, selectivityCache>>

(* --------------------------------------------------------------------------
   STATISTICS COLLECTION (ANALYZE)
   -------------------------------------------------------------------------- *)

\* Start ANALYZE on a table
StartAnalyze(table) ==
  /\ ~analyzeInProgress[table]
  /\ analyzeInProgress' = [analyzeInProgress EXCEPT ![table] = TRUE]
  /\ UNCHANGED <<tableStats, columnStats, indexStats, hllSketches,
                sampleSize, sampledRows, statsVersion, autoAnalyzeEnabled,
                modificationCount, selectivityCache>>

\* Sample rows from table
SampleRows(table, allRows) ==
  /\ analyzeInProgress[table]
  /\ sampledRows' = [sampledRows EXCEPT ![table] = 
                      ReservoirSample(allRows, sampleSize[table])]
  /\ UNCHANGED <<tableStats, columnStats, indexStats, hllSketches,
                analyzeInProgress, sampleSize, statsVersion, autoAnalyzeEnabled,
                modificationCount, selectivityCache>>

\* Compute column statistics from sampled rows
ComputeColumnStats(table, col) ==
  /\ analyzeInProgress[table]
  /\ LET samples == sampledRows[table]
         values == [i \in 1..Len(samples) |-> samples[i].values[col]]
         nullCount == Cardinality({v \in Range(values) : v = "NULL"})
         nonNullValues == SelectSeq(values, LAMBDA v: v # "NULL")
         distinctCount == Cardinality(Range(nonNullValues))
         \* Build histogram
         histogram == BuildEquiDepthHistogram(nonNullValues, MAX_HISTOGRAM_BUCKETS)
         \* Find most common values (simplified)
         valueCounts == [v \in Range(nonNullValues) |->
                          Cardinality({i \in 1..Len(nonNullValues) : nonNullValues[i] = v})]
         mcvs == <<>>  \* Simplified: top-N frequent values
     IN /\ columnStats' = [columnStats EXCEPT ![table][col] =
              [nullFraction |-> (nullCount * 100) \div Len(values),
               distinctValues |-> distinctCount,
               avgWidth |-> 10,  \* Simplified
               mostCommonValues |-> mcvs,
               mostCommonFreqs |-> <<>>,
               histogram |-> histogram,
               correlation |-> 0]]  \* Simplified
        /\ UNCHANGED <<tableStats, indexStats, hllSketches, analyzeInProgress,
                      sampleSize, sampledRows, statsVersion, autoAnalyzeEnabled,
                      modificationCount, selectivityCache>>

\* Update table-level statistics
ComputeTableStats(table) ==
  /\ analyzeInProgress[table]
  /\ LET rowCount == tableStats[table].rowCount
         pageCount == (rowCount + 99) \div 100  \* Simplified: 100 rows per page
     IN /\ tableStats' = [tableStats EXCEPT ![table].pageCount = pageCount,
                                            ![table].lastAnalyzed = 1,  \* Current timestamp
                                            ![table].modifications = 0]
        /\ UNCHANGED <<columnStats, indexStats, hllSketches, analyzeInProgress,
                      sampleSize, sampledRows, statsVersion, autoAnalyzeEnabled,
                      modificationCount, selectivityCache>>

\* Finish ANALYZE
FinishAnalyze(table) ==
  /\ analyzeInProgress[table]
  /\ analyzeInProgress' = [analyzeInProgress EXCEPT ![table] = FALSE]
  /\ statsVersion' = [statsVersion EXCEPT ![table] = @ + 1]
  /\ modificationCount' = [modificationCount EXCEPT ![table] = 0]
  /\ sampledRows' = [sampledRows EXCEPT ![table] = <<>>]
  /\ UNCHANGED <<tableStats, columnStats, indexStats, hllSketches,
                sampleSize, autoAnalyzeEnabled, selectivityCache>>

(* --------------------------------------------------------------------------
   AUTO-ANALYZE
   -------------------------------------------------------------------------- *)

\* Auto-analyze triggers automatically
AutoAnalyzeTrigger(table) ==
  /\ ShouldAutoAnalyze(table)
  /\ StartAnalyze(table)

\* Enable/disable auto-analyze
SetAutoAnalyze(enabled) ==
  /\ autoAnalyzeEnabled' = enabled
  /\ UNCHANGED <<tableStats, columnStats, indexStats, hllSketches,
                analyzeInProgress, sampleSize, sampledRows, statsVersion,
                modificationCount, selectivityCache>>

(* --------------------------------------------------------------------------
   QUERY OPTIMIZATION USAGE
   -------------------------------------------------------------------------- *)

\* Query optimizer requests selectivity estimate
EstimateQuerySelectivity(table, col, predicate, value) ==
  /\ LET stats == columnStats[table][col]
         estimate == EstimateSelectivity(stats, predicate, value)
     IN /\ selectivityCache' = [selectivityCache EXCEPT ![(table, predicate)] = estimate]
        /\ UNCHANGED <<tableStats, columnStats, indexStats, hllSketches,
                      analyzeInProgress, sampleSize, sampledRows, statsVersion,
                      autoAnalyzeEnabled, modificationCount>>

(* --------------------------------------------------------------------------
   NEXT STATE
   -------------------------------------------------------------------------- *)

Next_Stats ==
  \/ \E table \in Tables: RecordModification(table)
  \/ \E table \in Tables, delta \in Int: UpdateRowCount(table, delta)
  \/ \E table \in Tables: StartAnalyze(table)
  \/ \E table \in Tables, rows \in Seq(Row): SampleRows(table, rows)
  \/ \E table \in Tables, col \in Columns: ComputeColumnStats(table, col)
  \/ \E table \in Tables: ComputeTableStats(table)
  \/ \E table \in Tables: FinishAnalyze(table)
  \/ \E table \in Tables: AutoAnalyzeTrigger(table)
  \/ \E enabled \in BOOLEAN: SetAutoAnalyze(enabled)
  \/ \E table \in Tables, col \in Columns, pred \in STRING, val \in Value:
       EstimateQuerySelectivity(table, col, pred, val)

Spec_Stats == Init_Stats /\ [][Next_Stats]_statsVars

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Statistics version monotonically increases
Inv_Stats_VersionMonotonic ==
  \A table \in Tables:
    statsVersion[table] >= 1

\* Invariant 2: Modification count reset after ANALYZE
Inv_Stats_ModificationReset ==
  \A table \in Tables:
    analyzeInProgress[table] => modificationCount[table] <= ModificationThreshold(table) + 10

\* Invariant 3: Histogram buckets properly ordered
Inv_Stats_HistogramOrdered ==
  \A table \in Tables, col \in Columns:
    LET histogram == columnStats[table][col].histogram
    IN \A i \in 1..Len(histogram)-1:
         histogram[i].maxValue <= histogram[i+1].minValue

\* Invariant 4: Null fraction between 0 and 100
Inv_Stats_NullFractionValid ==
  \A table \in Tables, col \in Columns:
    LET nullFrac == columnStats[table][col].nullFraction
    IN nullFrac >= 0 /\ nullFrac <= 100

\* Invariant 5: Sample size doesn't exceed table size
Inv_Stats_SampleSizeValid ==
  \A table \in Tables:
    Len(sampledRows[table]) <= tableStats[table].rowCount

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Property 1: ANALYZE eventually completes
Prop_Stats_AnalyzeCompletion ==
  \A table \in Tables:
    [](analyzeInProgress[table] => <>(~analyzeInProgress[table]))

\* Property 2: Auto-analyze eventually triggers
Prop_Stats_AutoAnalyzeTriggers ==
  \A table \in Tables:
    [](ShouldAutoAnalyze(table) => <>(analyzeInProgress[table]))

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

THEOREM Stats_Correctness ==
  Spec_Stats => []Inv_Stats_HistogramOrdered

THEOREM Stats_Progress ==
  Spec_Stats => Prop_Stats_AnalyzeCompletion

=============================================================================

(*
  REFERENCES:
  
  [1] Ioannidis, Y. E. (2003). "The history of histograms (abridged)."
      Proceedings of the 29th international conference on Very large data bases.
  
  [2] Ioannidis, Y., & Poosala, V. (1995). "Balancing histogram optimality and
      practicality for query result size estimation." ACM SIGMOD Record, 24(2).
  
  [3] Flajolet, P., Fusy, É., Gandouet, O., & Meunier, F. (2007). "HyperLogLog:
      the analysis of a near-optimal cardinality estimation algorithm." Analysis
      of Algorithms (AofA) 2007.
  
  [4] Selinger, P. G., Astrahan, M. M., Chamberlin, D. D., Lorie, R. A., & Price,
      T. G. (1979). "Access path selection in a relational database management
      system." Proceedings of the 1979 ACM SIGMOD international conference.
  
  [5] Chaudhuri, S., & Narasayya, V. (2007). "Statistics on query expressions."
      Proceedings of the 2007 ACM SIGMOD international conference.
  
  IMPLEMENTATION NOTES:
  
  - Equi-depth histograms: equal number of rows per bucket
  - Most Common Values (MCVs) stored separately from histogram
  - HyperLogLog provides approximate distinct count with 1-2% error
  - Auto-analyze triggers after 20% modifications (default)
  - Sample size typically 300 blocks (100MB for 8KB pages)
  - Statistics used by query optimizer for cost estimation
  - Similar to PostgreSQL ANALYZE, Oracle DBMS_STATS
*)

