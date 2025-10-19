-------------------------- MODULE APFSOptimizations --------------------------
(*****************************************************************************)
(* APFS (Apple File System) Optimizations for ColibrìDB                     *)
(*                                                                           *)
(* Models Copy-on-Write, clones, snapshots specific to APFS                *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Apple APFS Reference (2017)                                          *)
(*   - Rodeh (2008): "B-trees, Shadowing, and Clones"                       *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS MaxFiles, MaxSnapshots, MaxClones

VARIABLES
    files,              \* File system state
    snapshots,          \* Snapshots
    clones,             \* Cloned files
    refCounts           \* Reference counts for COW

vars == <<files, snapshots, clones, refCounts>>

Init ==
    /\ files = [f \in {} |-> <<>>]
    /\ snapshots = {}
    /\ clones = {}
    /\ refCounts = [f \in {} |-> 0]

WriteFile(fileId, data) ==
    /\ Cardinality(DOMAIN files) < MaxFiles
    /\ files' = files @@ (fileId :> data)
    /\ refCounts' = refCounts @@ (fileId :> 1)
    /\ UNCHANGED <<snapshots, clones>>

CreateSnapshot(snapId) ==
    /\ Cardinality(snapshots) < MaxSnapshots
    /\ snapId \notin snapshots
    /\ snapshots' = snapshots \cup {snapId}
    /\ UNCHANGED <<files, clones, refCounts>>

CloneFile(sourceId, targetId) ==
    /\ sourceId \in DOMAIN files
    /\ targetId \notin DOMAIN files
    /\ Cardinality(clones) < MaxClones
    /\ files' = files @@ (targetId :> files[sourceId])
    /\ clones' = clones \cup {[source |-> sourceId, target |-> targetId]}
    /\ refCounts' = [refCounts EXCEPT ![sourceId] = @ + 1]
    /\ UNCHANGED snapshots

ValidRefCounts ==
    \A f \in DOMAIN refCounts : refCounts[f] >= 0

Next ==
    \/ \E fid \in Nat, d \in STRING : WriteFile(fid, d)
    \/ \E sid \in Nat : CreateSnapshot(sid)
    \/ \E src, tgt \in Nat : CloneFile(src, tgt)

Spec == Init /\ [][Next]_vars

THEOREM APFSCorrectness == Spec => []ValidRefCounts

================================================================================

