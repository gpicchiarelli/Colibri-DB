---------------------------- MODULE FaultInjection ----------------------------
(*****************************************************************************)
(* Fault Injection for Chaos Testing in ColibrìDB                           *)
(* Models injecting faults: crashes, delays, packet loss, disk errors       *)
(* Author: ColibrìDB Development Team | Date: 2025-10-19                    *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS Nodes, FaultTypes

VARIABLES faults, nodeState, injectedFaults

vars == <<faults, nodeState, injectedFaults>>

Init ==
    /\ faults = {}
    /\ nodeState = [n \in Nodes |-> "HEALTHY"]
    /\ injectedFaults = 0

InjectFault(node, faultType) ==
    /\ node \in Nodes
    /\ faultType \in FaultTypes
    /\ nodeState[node] = "HEALTHY"
    /\ faults' = faults \cup {[node |-> node, type |-> faultType]}
    /\ nodeState' = [nodeState EXCEPT ![node] = "FAULTY"]
    /\ injectedFaults' = injectedFaults + 1

RecoverNode(node) ==
    /\ nodeState[node] = "FAULTY"
    /\ nodeState' = [nodeState EXCEPT ![node] = "HEALTHY"]
    /\ faults' = {f \in faults : f.node # node}
    /\ UNCHANGED injectedFaults

NodesEventuallyRecover ==
    \A n \in Nodes : nodeState[n] = "FAULTY" ~> nodeState[n] = "HEALTHY"

Next ==
    \/ \E n \in Nodes, ft \in FaultTypes : InjectFault(n, ft)
    \/ \E n \in Nodes : RecoverNode(n)

Spec == Init /\ [][Next]_vars
THEOREM Correctness == Spec => NodesEventuallyRecover
================================================================================

