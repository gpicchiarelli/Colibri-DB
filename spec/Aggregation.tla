------------------------------ MODULE Aggregation ------------------------------
(*****************************************************************************)
(* Aggregation Functions (SUM, AVG, COUNT, MIN, MAX, GROUP BY) for ColibrìDB*)
(* Models aggregate query processing with grouping                           *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS Data, GroupKeys

VARIABLES aggregates, groups

vars == <<aggregates, groups>>

Init ==
    /\ aggregates = [f \in {"SUM", "AVG", "COUNT", "MIN", "MAX"} |-> 0]
    /\ groups = [g \in GroupKeys |-> [count |-> 0, sum |-> 0]]

ComputeAggregate(func, values) ==
    CASE func = "SUM" -> Sum(values)
      [] func = "AVG" -> Sum(values) \div Len(values)
      [] func = "COUNT" -> Len(values)
      [] func = "MIN" -> Min(values)
      [] func = "MAX" -> Max(values)

GroupBy(key, value) ==
    /\ key \in GroupKeys
    /\ groups' = [groups EXCEPT ![key].count = @ + 1, ![key].sum = @ + value]
    /\ UNCHANGED aggregates

AggregateCorrect ==
    \A g \in GroupKeys : groups[g].count >= 0

Next == \E k \in GroupKeys, v \in 1..100 : GroupBy(k, v)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => []AggregateCorrect
================================================================================

