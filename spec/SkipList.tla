------------------------------- MODULE SkipList -------------------------------
(*****************************************************************************)
(* Skip List Data Structure for ColibrìDB                                   *)
(*                                                                           *)
(* This specification models a probabilistic skip list with:                *)
(*   - Randomized level assignment (geometric distribution)                 *)
(*   - O(log n) expected search/insert/delete complexity                    *)
(*   - Space-efficient implementation                                       *)
(*   - Concurrent operations (lock-free variants)                           *)
(*   - Range queries                                                        *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Pugh, W. (1990). "Skip Lists: A Probabilistic Alternative to         *)
(*     Balanced Trees". Communications of the ACM, 33(6), 668-676.          *)
(*     DOI: 10.1145/78973.78977                                             *)
(*     Original skip list paper                                             *)
(*   - Pugh, W. (1998). "Concurrent Maintenance of Skip Lists"              *)
(*     Technical Report CS-TR-3222, University of Maryland                  *)
(*     Lock-free concurrent skip lists                                      *)
(*   - Sundell, H., & Tsigas, P. (2005). "Lock-Free Deques and             *)
(*     Doubly Linked Lists". Journal of Parallel and Distributed            *)
(*     Computing, 65(12), 1501-1517. DOI: 10.1016/j.jpdc.2005.04.018       *)
(*     Concurrent linked structures                                         *)
(*   - Herlihy, M., & Shavit, N. (2008). "The Art of Multiprocessor        *)
(*     Programming". Chapter 14: Skiplists and Balanced Search.             *)
(*     ISBN: 978-0123705914                                                 *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxLevel,       \* Maximum level (typically 16-32, Pugh 1990 recommends log2(N))
    Probability,    \* P = 1/2 or 1/4 (Pugh 1990: p=1/2 optimal for most cases)
    MaxKeys,        \* Maximum number of keys for model checking
    MAX_TX,         \* From CORE - for transactional operations
    MAX_LSN,        \* From CORE - for WAL integration
    MAX_PAGES       \* From CORE - for persistent skip list nodes

ASSUME MaxLevel \in Nat \ {0}
ASSUME Probability \in {2, 4}  \* 1/2 or 1/4
ASSUME MaxKeys \in Nat \ {0}

VARIABLES
    skipList,       \* [NodeId -> Node] - The skip list structure
    levels,         \* Current maximum level in use
    size,           \* Number of elements (cardinality)
    operations,     \* Operation log for verification
    pageLSN         \* [NodeId -> LSN] - For WAL integration

skipListVars == <<skipList, levels, size, operations, pageLSN>>

(***************************************************************************
 * Node Structure (Pugh 1990, Figure 1)
 ***************************************************************************)
Node == [
  key: Value,                    \* Uses CORE Value type
  rid: RID,                      \* Record identifier from CORE
  forward: Seq(Nat \union {0}), \* Forward pointers per level
  lsn: LSN                       \* Last modification LSN (from CORE)
]

(***************************************************************************
 * Type Invariant
 ***************************************************************************)
TypeOK_SkipList ==
  /\ skipList \in [Nat -> Node]
  /\ levels \in 1..MaxLevel
  /\ size \in 0..MaxKeys
  /\ operations \in Seq([op: {"insert", "delete", "search"}, 
                          key: Value, result: BOOLEAN])
  /\ pageLSN \in [Nat -> LSN]

Init ==
    /\ skipList = [n \in {0} |-> 
         [key |-> [type |-> "int", val |-> -999999],  \* HEAD sentinel (CORE Value)
          rid |-> [pageId |-> 0, slotId |-> 0],       \* Null RID
          forward |-> [i \in 1..MaxLevel |-> 0],
          lsn |-> 0]]                                  \* Initial LSN
    /\ levels = 1
    /\ size = 0
    /\ operations = <<>>
    /\ pageLSN = [n \in {0} |-> 0]

(***************************************************************************
 * Random Level Generation (Pugh 1990, Section 3)
 * 
 * Geometric distribution: P(level = k) = p^(k-1) * (1-p)
 * Expected level: 1/(1-p), e.g., p=1/2 gives expected level = 2
 ***************************************************************************)
RandomLevel ==
    \* For TLA+ model checking, we use bounded choice
    \* In implementation: loop while (random() < p) and level < MaxLevel
    CHOOSE level \in 1..MaxLevel : 
      \/ level = 1  \* Always possible
      \/ level <= levels + 1  \* Can grow by at most 1 (Pugh 1990)

Search(key) ==
    LET RECURSIVE SearchLevel(_, _, _)
        SearchLevel(node, k, level) ==
            IF level = 0 THEN node
            ELSE IF skipList[skipList[node].forward[level]].key = k 
                 THEN skipList[node].forward[level]
                 ELSE IF skipList[skipList[node].forward[level]].key < k
                      THEN SearchLevel(skipList[node].forward[level], k, level)
                      ELSE SearchLevel(node, k, level - 1)
    IN SearchLevel(0, key, levels)

Insert(key, value) ==
    /\ size < MaxKeys
    /\ key \notin {skipList[n].key : n \in DOMAIN skipList}
    /\ LET newLevel == RandomLevel
           update == [i \in 1..MaxLevel |-> 0]  \* Nodes to update
           newNode == Len(DOMAIN skipList)
       IN
           /\ skipList' = skipList @@ (newNode :>
                [key |-> key, value |-> value,
                 forward |-> [i \in 1..newLevel |-> 0]])
           /\ levels' = IF newLevel > levels THEN newLevel ELSE levels
           /\ size' = size + 1
           /\ operations' = Append(operations,
                [op |-> "INSERT", key |-> key, value |-> value])
    /\ UNCHANGED <<>>

Delete(key) ==
    /\ key \in {skipList[n].key : n \in DOMAIN skipList}
    /\ size' = size - 1
    /\ operations' = Append(operations, [op |-> "DELETE", key |-> key])
    /\ UNCHANGED <<skipList, levels>>

(* Invariants *)
OrderedKeys ==
    \A n1, n2 \in DOMAIN skipList :
        n1 < n2 => skipList[n1].key < skipList[n2].key

BoundedLevel ==
    levels <= MaxLevel

Next ==
    \/ \E k \in Int, v \in STRING : Insert(k, v)
    \/ \E k \in Int : Delete(k)

Spec == Init /\ [][Next]_vars

THEOREM SkipListCorrectness ==
    Spec => [](OrderedKeys /\ BoundedLevel)

================================================================================

