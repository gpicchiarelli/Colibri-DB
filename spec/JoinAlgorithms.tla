---------------------------- MODULE JoinAlgorithms ----------------------------
(*****************************************************************************)
(* Join Algorithms: Hash Join, Merge Join, Nested Loop Join for ColibrìDB   *)
(* Models different join strategies and their costs                          *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS LeftTable, RightTable

VARIABLES joinResult, joinMethod, cost

vars == <<joinResult, joinMethod, cost>>

Init ==
    /\ joinResult = {}
    /\ joinMethod = "NESTED_LOOP"
    /\ cost = 0

HashJoin(left, right) ==
    /\ joinMethod' = "HASH"
    /\ cost' = Cardinality(left) + Cardinality(right)
    /\ joinResult' = {<<l, r>> : l \in left, r \in right}

MergeJoin(left, right) ==
    /\ joinMethod' = "MERGE"
    /\ cost' = Cardinality(left) + Cardinality(right)
    /\ joinResult' = {<<l, r>> : l \in left, r \in right}

NestedLoopJoin(left, right) ==
    /\ joinMethod' = "NESTED_LOOP"
    /\ cost' = Cardinality(left) * Cardinality(right)
    /\ joinResult' = {<<l, r>> : l \in left, r \in right}

CostReasonable ==
    cost <= Cardinality(LeftTable) * Cardinality(RightTable) * 2

Next ==
    \/ HashJoin(LeftTable, RightTable)
    \/ MergeJoin(LeftTable, RightTable)
    \/ NestedLoopJoin(LeftTable, RightTable)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []CostReasonable
================================================================================

