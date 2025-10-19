----------------------------- MODULE QueryPipeline -----------------------------
(*
  Query Pipeline Bridge Module
  
  Integrates complete SQL query processing pipeline:
  - SQLParser: SQL statement parsing
  - TypeSystem: Type checking and validation
  - QueryOptimizer: Cost-based optimization
  - QueryExecutor: Physical query execution
  - PreparedStatements: Prepared statement caching
  - JoinAlgorithms: Hash join, merge join, nested loop
  - Aggregation: GROUP BY, aggregates
  - Materialization: Materialized views
  - WindowFunctions: OLAP window functions
  - StatisticsMaintenance: Query statistics
  
  Complete SQL pipeline: Parse → Type Check → Optimize → Execute
  
  Cross-Module Invariants:
  1. Type Safety: Execution matches type-checked plan
  2. Optimization Correctness: Optimized plan semantically equivalent
  3. Result Correctness: Results match SQL semantics
  4. Statistics Freshness: Statistics used in optimization are recent
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS CORE, SQLParser, TypeSystem, QueryOptimizer, QueryExecutor,
        PreparedStatements, JoinAlgorithms, Aggregation, Materialization,
        WindowFunctions, StatisticsMaintenance

CONSTANTS
  MAX_QUERY_COMPLEXITY    \* Maximum query complexity score

VARIABLES
  queryPipeline,          \* [QueryId -> [stage, ast, plan, result]]
  executionStats,         \* [QueryId -> [time, rows, cost]]
  preparedCache,          \* [PreparedId -> CachedPlan]
  pipelineStage           \* Current pipeline stage

pipelineVars == <<queryPipeline, executionStats, preparedCache, pipelineStage>>

allVars == <<parserVars, typeVars, optimizerVars, executorVars, preparedVars,
             joinVars, aggVars, matVars, windowVars, statsVars, pipelineVars>>

TypeOK_Pipeline ==
  /\ queryPipeline \in [QueryIds -> [
       stage: {"parse", "typecheck", "optimize", "execute", "done", "error"},
       ast: ASTNode,
       plan: PhysicalPlan,
       result: ResultSet
     ]]
  /\ executionStats \in [QueryIds -> [time: Nat, rows: Nat, cost: Nat]]
  /\ preparedCache \in [PreparedIds -> CachedPlan]
  /\ pipelineStage \in {"parse", "typecheck", "optimize", "execute", "done"}

Init_Pipeline ==
  /\ Init_Parser /\ Init_TypeSystem /\ Init_QueryOptimizer /\ Init_QueryExecutor
  /\ Init_PreparedStatements /\ Init_JoinAlgorithms /\ Init_Aggregation
  /\ Init_Materialization /\ Init_WindowFunctions /\ Init_Stats
  /\ queryPipeline = [qid \in QueryIds |-> [
       stage |-> "parse", ast |-> [kind |-> "empty"], 
       plan |-> [kind |-> "none"], result |-> <<>>]]
  /\ executionStats = [qid \in QueryIds |-> [time |-> 0, rows |-> 0, cost |-> 0]]
  /\ preparedCache = [pid \in PreparedIds |-> [plan |-> [kind |-> "none"], valid |-> FALSE]]
  /\ pipelineStage = "parse"

\* Stage 1: Parse SQL
ParseQuery(qid, sqlString) ==
  /\ Parse(sqlString)  \* From SQLParser
  /\ queryPipeline' = [queryPipeline EXCEPT ![qid] = 
       [@ EXCEPT !.stage = "typecheck", !.ast = ast]]
  /\ UNCHANGED <<executionStats, preparedCache, pipelineStage>>

\* Stage 2: Type Check
TypeCheckQuery(qid) ==
  /\ queryPipeline[qid].stage = "typecheck"
  /\ LET typeCheckResult == TypeCheck(queryPipeline[qid].ast, currentContext)
     IN IF typeCheckResult.valid
        THEN queryPipeline' = [queryPipeline EXCEPT ![qid].stage = "optimize"]
        ELSE queryPipeline' = [queryPipeline EXCEPT ![qid].stage = "error"]
  /\ UNCHANGED <<executionStats, preparedCache, pipelineStage>>

\* Stage 3: Optimize
OptimizeQuery(qid) ==
  /\ queryPipeline[qid].stage = "optimize"
  /\ LET stats == GetTableStats()  \* From StatisticsMaintenance
         logicalPlan == CreateLogicalPlan(queryPipeline[qid].ast)
         physicalPlan == Optimize(logicalPlan, stats)  \* From QueryOptimizer
     IN queryPipeline' = [queryPipeline EXCEPT ![qid] = 
          [@ EXCEPT !.stage = "execute", !.plan = physicalPlan]]
  /\ UNCHANGED <<executionStats, preparedCache, pipelineStage>>

\* Stage 4: Execute
ExecuteQuery(qid) ==
  /\ queryPipeline[qid].stage = "execute"
  /\ LET plan == queryPipeline[qid].plan
         result == ExecutePlan(plan)  \* From QueryExecutor
     IN /\ queryPipeline' = [queryPipeline EXCEPT ![qid] = 
              [@ EXCEPT !.stage = "done", !.result = result]]
        /\ executionStats' = [executionStats EXCEPT ![qid] = 
              [time |-> MeasureExecutionTime(), rows |-> Len(result), 
               cost |-> EstimateCost(plan)]]
  /\ UNCHANGED <<preparedCache, pipelineStage>>

\* Complete pipeline for complex query
ExecuteComplexQuery(qid, sqlString) ==
  /\ ParseQuery(qid, sqlString)
  /\ TypeCheckQuery(qid)
  /\ OptimizeQuery(qid)
  /\ ExecuteQuery(qid)

(* Prepared Statements *)
PrepareStatement(prepId, sqlString) ==
  /\ ParseQuery(999, sqlString)
  /\ TypeCheckQuery(999)
  /\ OptimizeQuery(999)
  /\ preparedCache' = [preparedCache EXCEPT ![prepId] = 
       [plan |-> queryPipeline[999].plan, valid |-> TRUE]]
  /\ UNCHANGED <<queryPipeline, executionStats, pipelineStage>>

ExecutePreparedStatement(qid, prepId, params) ==
  /\ preparedCache[prepId].valid
  /\ LET plan == preparedCache[prepId].plan
         result == ExecutePlanWithParams(plan, params)
     IN queryPipeline' = [queryPipeline EXCEPT ![qid] = 
          [stage |-> "done", ast |-> [kind |-> "empty"], 
           plan |-> plan, result |-> result]]
  /\ UNCHANGED <<executionStats, preparedCache, pipelineStage>>

Next_Pipeline ==
  \/ \E qid \in QueryIds, sql \in STRING: ParseQuery(qid, sql)
  \/ \E qid \in QueryIds: TypeCheckQuery(qid)
  \/ \E qid \in QueryIds: OptimizeQuery(qid)
  \/ \E qid \in QueryIds: ExecuteQuery(qid)
  \/ \E prepId \in PreparedIds, sql \in STRING: PrepareStatement(prepId, sql)
  \/ \E qid \in QueryIds, prepId \in PreparedIds, params \in Seq(Value):
       ExecutePreparedStatement(qid, prepId, params)
  \/ Next_Parser \/ Next_TypeSystem \/ Next_QueryOptimizer \/ Next_QueryExecutor
  \/ Next_PreparedStatements \/ Next_JoinAlgorithms \/ Next_Aggregation
  \/ Next_Materialization \/ Next_WindowFunctions \/ Next_Stats

Spec_Pipeline == Init_Pipeline /\ [][Next_Pipeline]_allVars

\* Invariant: Type safety
Inv_Pipeline_TypeSafety ==
  \A qid \in QueryIds:
    queryPipeline[qid].stage = "execute" =>
      TypeCheck(queryPipeline[qid].ast, currentContext).valid

\* Invariant: Optimization correctness
Inv_Pipeline_OptimizationCorrectness ==
  \A qid \in QueryIds:
    queryPipeline[qid].stage = "done" =>
      SemanticallyEquivalent(queryPipeline[qid].ast, queryPipeline[qid].plan)

THEOREM Pipeline_TypeSafety ==
  Spec_Pipeline => []Inv_Pipeline_TypeSafety

=============================================================================

