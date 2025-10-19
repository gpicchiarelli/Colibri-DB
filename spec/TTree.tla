-------------------------------- MODULE TTree --------------------------------
(*****************************************************************************)
(* T-Tree: Binary Search Tree optimized for main-memory databases          *)
(*                                                                           *)
(* Based on:                                                                 *)
(*   - Lehman, T. J., & Carey, M. J. (1986). "A Study of Index Structures  *)
(*     for Main Memory Database Management Systems"                         *)
(*     Proceedings of VLDB '86, pp. 294-303.                                *)
(*     Original T-Tree paper                                                *)
(*   - Rao, J., & Ross, K. A. (2000). "Making B+-Trees Cache Conscious     *)
(*     in Main Memory". Proceedings of SIGMOD '00, pp. 475-486.             *)
(*     DOI: 10.1145/342009.335449                                           *)
(*     Cache-conscious index structures                                     *)
(*   - Designed for CPU cache efficiency with cache line alignment          *)
(*   - Stores multiple keys per node (like B-tree but binary structure)    *)
(*   - Each node contains min..max range for fast filtering                *)
(*   - Hybrid: combines B-tree storage with BST navigation                  *)
(*                                                                           *)
(* Author: ColibrìDB Development Team                                        *)
(* Date: 2025-10-19                                                          *)
(*****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MinKeys,        \* Minimum keys per node (Lehman & Carey: typically CPU_CACHE_LINE / sizeof(key))
    MaxKeys,        \* Maximum keys per node (Lehman & Carey: ~16-32 for cache line fit)
    TotalKeys,      \* Total keys in tree (for model checking)
    MAX_TX,         \* From CORE
    MAX_LSN,        \* From CORE
    MAX_PAGES       \* From CORE

ASSUME MinKeys \in Nat \ {0}
ASSUME MaxKeys \in Nat \ {0}
ASSUME MinKeys <= MaxKeys
ASSUME TotalKeys \in Nat

VARIABLES
    tree,           \* [NodeId -> Node] - Tree structure
    root,           \* Root node ID (PageId from CORE)
    nodeCount,      \* Number of nodes
    operations,     \* Operation log for verification
    nodeLSN         \* [NodeId -> LSN] - For WAL integration

ttreeVars == <<tree, root, nodeCount, operations, nodeLSN>>

(***************************************************************************
 * T-Tree Node Structure (Lehman & Carey 1986, Figure 3)
 * 
 * Each node stores:
 * - keys[]: Array of keys (sorted)
 * - rids[]: Corresponding record IDs
 * - left, right: Binary tree pointers
 * - min, max: Bounding values for fast filtering
 * - lsn: Last modification LSN
 ***************************************************************************)
Node == [
    keys: Seq(Value),              \* Uses CORE Value type
    rids: Seq(RID),                \* Record identifiers from CORE
    left: PageId \union {0},       \* Left child (uses CORE PageId)
    right: PageId \union {0},      \* Right child (uses CORE PageId)
    min: Value,                    \* Minimum key in subtree
    max: Value,                    \* Maximum key in subtree
    lsn: LSN                       \* Last modification LSN (from CORE)
]

Init ==
    /\ tree = [n \in {1} |-> 
         [keys |-> <<>>, values |-> <<>>, left |-> 0, right |-> 0,
          min |-> 0, max |-> 0]]
    /\ root = 1
    /\ nodeCount = 1
    /\ operations = <<>>

Search(key) ==
    LET RECURSIVE SearchNode(_,_)
        SearchNode(nodeId, k) ==
            IF nodeId = 0 THEN 0
            ELSE LET node == tree[nodeId]
                 IN IF k < node.min THEN SearchNode(node.left, k)
                    ELSE IF k > node.max THEN SearchNode(node.right, k)
                    ELSE nodeId  \* Key in this node's range
    IN SearchNode(root, key)

Insert(key, value) ==
    /\ nodeCount < TotalKeys \div MinKeys
    /\ operations' = Append(operations, [op |-> "INSERT", key |-> key])
    /\ UNCHANGED <<tree, root, nodeCount>>

(* Invariants *)
ValidRanges ==
    \A n \in DOMAIN tree :
        tree[n].keys # <<>> =>
            /\ tree[n].min = Head(tree[n].keys)
            /\ tree[n].max = tree[n].keys[Len(tree[n].keys)]

BSTProperty ==
    \A n \in DOMAIN tree :
        /\ tree[n].left # 0 => tree[tree[n].left].max < tree[n].min
        /\ tree[n].right # 0 => tree[tree[n].right].min > tree[n].max

Next == \E k \in Int, v \in STRING : Insert(k, v)

Spec == Init /\ [][Next]_vars

THEOREM TTreeCorrectness == Spec => [](ValidRanges /\ BSTProperty)

================================================================================

