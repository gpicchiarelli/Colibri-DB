--------------------------- MODULE DistributedQuery ---------------------------
(*****************************************************************************)
(* Distributed Query Processing (Map-Reduce style) for ColibrìDB            *)
(* Models query distribution, execution, and result aggregation              *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS Nodes, QueryFragments

VARIABLES fragments, results, aggregatedResult, phase

vars == <<fragments, results, aggregatedResult, phase>>

Init ==
    /\ fragments = [n \in Nodes |-> {}]
    /\ results = [n \in Nodes |-> {}]
    /\ aggregatedResult = {}
    /\ phase = "MAP"

DistributeQuery(node, fragment) ==
    /\ phase = "MAP"
    /\ node \in Nodes
    /\ fragment \in QueryFragments
    /\ fragments' = [fragments EXCEPT ![node] = @ \cup {fragment}]
    /\ UNCHANGED <<results, aggregatedResult, phase>>

ExecuteFragment(node) ==
    /\ phase = "MAP"
    /\ node \in Nodes
    /\ fragments[node] # {}
    /\ results' = [results EXCEPT ![node] = fragments[node]]
    /\ fragments' = [fragments EXCEPT ![node] = {}]
    /\ UNCHANGED <<aggregatedResult, phase>>

AggregateResults ==
    /\ phase = "MAP"
    /\ \A n \in Nodes : fragments[n] = {}
    /\ aggregatedResult' = UNION {results[n] : n \in Nodes}
    /\ phase' = "REDUCE"
    /\ UNCHANGED <<fragments, results>>

QueryComplete ==
    phase = "REDUCE" /\ aggregatedResult # {}

Next ==
    \/ \E n \in Nodes, f \in QueryFragments : DistributeQuery(n, f)
    \/ \E n \in Nodes : ExecuteFragment(n)
    \/ AggregateResults

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => <>(QueryComplete)
================================================================================

