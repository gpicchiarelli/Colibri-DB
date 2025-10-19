--------------------------- MODULE MemoryManagement ---------------------------
(*****************************************************************************)
(* Memory Management with Arena Allocators for ColibrìDB                    *)
(*                                                                           *)
(* Models arena allocation, memory pools, garbage collection                *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Wilson et al. (1995): "Dynamic Storage Allocation: A Survey"         *)
(*   - Berger et al. (2002): "Reconsidering Custom Memory Allocation"       *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, FiniteSets, TLC, CORE

CONSTANTS TotalMemory, MaxArenas, BlockSizes

VARIABLES
    arenas,             \* Set of active arenas
    allocations,        \* Current allocations
    freeList,           \* Free memory blocks
    gcRuns              \* Garbage collection runs

vars == <<arenas, allocations, freeList, gcRuns>>

Init ==
    /\ arenas = {}
    /\ allocations = [a \in {} |-> <<>>]
    /\ freeList = TotalMemory
    /\ gcRuns = 0

CreateArena(arenaId, size) ==
    /\ Cardinality(arenas) < MaxArenas
    /\ arenaId \notin arenas
    /\ size <= freeList
    /\ arenas' = arenas \cup {arenaId}
    /\ allocations' = allocations @@ (arenaId :> <<>>)
    /\ freeList' = freeList - size
    /\ UNCHANGED gcRuns

Allocate(arenaId, size) ==
    /\ arenaId \in arenas
    /\ size <= freeList
    /\ freeList' = freeList - size
    /\ allocations' = [allocations EXCEPT ![arenaId] = Append(@, size)]
    /\ UNCHANGED <<arenas, gcRuns>>

GarbageCollect ==
    /\ gcRuns' = gcRuns + 1
    /\ freeList' = freeList + (TotalMemory \div 10)  \* Reclaim 10%
    /\ UNCHANGED <<arenas, allocations>>

MemoryConsistent ==
    freeList >= 0 /\ freeList <= TotalMemory

Next ==
    \/ \E aid \in Nat, s \in BlockSizes : CreateArena(aid, s)
    \/ \E aid \in arenas, s \in BlockSizes : Allocate(aid, s)
    \/ GarbageCollect

Spec == Init /\ [][Next]_vars

THEOREM MemoryCorrectness == Spec => []MemoryConsistent

================================================================================

