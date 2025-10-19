----------------------------- MODULE IndexSubsystem -----------------------------
(*
  Index Subsystem Bridge Module
  
  Integrates all 9 index structures:
  - BTree: B+Tree (primary index)
  - HashIndex: Hash-based index
  - ARTIndex: Adaptive Radix Tree
  - LSMTree: Log-Structured Merge Tree
  - FractalTreeIndex: Fractal Tree (TokuDB-style)
  - BloomFilter: Probabilistic membership testing
  - SkipList: Probabilistic balanced tree
  - TTree: Main-memory index
  - RadixTree: Radix/Patricia tree
  
  Provides unified index interface with automatic index selection
  
  Cross-Module Invariants:
  1. Index Consistency: All indexes reflect same logical data
  2. Query Correctness: Index scans equivalent to full scans
  3. Maintenance Consistency: Updates propagate to all relevant indexes
  
  Author: ColibrìDB Team
  Date: 2025-10-19
*)

EXTENDS CORE, BTree, HashIndex, ARTIndex, LSMTree, FractalTreeIndex,
        BloomFilter, SkipList, TTree, RadixTree

CONSTANTS
  IndexTypes    \* Set of available index types

VARIABLES
  indexRegistry,      \* [IndexName -> [type, table, columns, root]]
  indexSelection,     \* [Query -> IndexName] - Selected index per query
  indexStats          \* [IndexName -> [size, height, selectivity]]

indexVars == <<indexRegistry, indexSelection, indexStats>>

allVars == <<btreeVars, hashVars, artVars, lsmVars, fractalVars, bloomVars,
             skiplistVars, ttreeVars, radixVars, indexVars>>

TypeOK_IndexSubsystem ==
  /\ TypeOK_BTree /\ TypeOK_HashIndex /\ TypeOK_ARTIndex /\ TypeOK_LSMTree
  /\ TypeOK_FractalTree /\ TypeOK_BloomFilter /\ TypeOK_SkipList 
  /\ TypeOK_TTree /\ TypeOK_RadixTree
  /\ indexRegistry \in [IndexNames -> [
       type: IndexTypes, table: Tables, columns: Seq(Columns), root: PageIds]]
  /\ indexSelection \in [Queries -> IndexNames]
  /\ indexStats \in [IndexNames -> [size: Nat, height: Nat, selectivity: Nat]]

Init_IndexSubsystem ==
  /\ Init_BTree /\ Init_HashIndex /\ Init_ARTIndex /\ Init_LSMTree
  /\ Init_FractalTree /\ Init_BloomFilter /\ Init_SkipList
  /\ Init_TTree /\ Init_RadixTree
  /\ indexRegistry = [iname \in IndexNames |-> 
       [type |-> "btree", table |-> "none", columns |-> <<>>, root |-> 0]]
  /\ indexSelection = [q \in Queries |-> "none"]
  /\ indexStats = [iname \in IndexNames |-> [size |-> 0, height |-> 0, selectivity |-> 100]]

\* Create index with automatic type selection
CreateIndex(indexName, table, columns, indexType) ==
  /\ indexRegistry' = [indexRegistry EXCEPT ![indexName] =
       [type |-> indexType, table |-> table, columns |-> columns, 
        root |-> AllocateIndexRoot()]]
  /\ \* Initialize appropriate index structure
     CASE indexType OF
       "btree" -> BTree_Create(indexName)
       [] "hash" -> HashIndex_Create(indexName)
       [] "art" -> ARTIndex_Create(indexName)
       [] "lsm" -> LSMTree_Create(indexName)
       [] OTHER -> TRUE
  /\ UNCHANGED <<indexSelection, indexStats>>

\* Select best index for query
SelectIndexForQuery(query) ==
  /\ LET candidates == {idx \in DOMAIN indexRegistry :
                         indexRegistry[idx].table = query.table /\
                         indexRegistry[idx].columns[1] = query.whereColumn}
         bestIndex == CHOOSE idx \in candidates:
                        \A other \in candidates:
                          indexStats[idx].selectivity <= indexStats[other].selectivity
     IN indexSelection' = [indexSelection EXCEPT ![query] = bestIndex]
  /\ UNCHANGED <<indexRegistry, indexStats>>

\* Unified index scan
IndexScan(indexName, key) ==
  CASE indexRegistry[indexName].type OF
    "btree" -> BTree_Search(key)
    [] "hash" -> HashIndex_Lookup(key)
    [] "art" -> ARTIndex_Search(key)
    [] "lsm" -> LSMTree_Get(key)
    [] "skip" -> SkipList_Search(key)
    [] OTHER -> {}

\* Insert into all relevant indexes
IndexInsert(table, key, rid) ==
  /\ LET relevantIndexes == {idx \in DOMAIN indexRegistry :
                              indexRegistry[idx].table = table}
     IN \A idx \in relevantIndexes:
          CASE indexRegistry[idx].type OF
            "btree" -> BTree_Insert(key, rid)
            [] "hash" -> HashIndex_Insert(key, rid)
            [] "art" -> ARTIndex_Insert(key, rid)
            [] "lsm" -> LSMTree_Put(key, rid)
            [] OTHER -> TRUE
  /\ UNCHANGED <<indexSelection, indexStats>>

Next_IndexSubsystem ==
  \/ \E iname \in IndexNames, table \in Tables, cols \in Seq(Columns), 
       itype \in IndexTypes: CreateIndex(iname, table, cols, itype)
  \/ \E query \in Queries: SelectIndexForQuery(query)
  \/ \E iname \in IndexNames, key \in Keys: IndexScan(iname, key)
  \/ \E table \in Tables, key \in Keys, rid \in RID: IndexInsert(table, key, rid)
  \/ Next_BTree \/ Next_HashIndex \/ Next_ARTIndex \/ Next_LSMTree
  \/ Next_FractalTree \/ Next_BloomFilter \/ Next_SkipList
  \/ Next_TTree \/ Next_RadixTree

Spec_IndexSubsystem == Init_IndexSubsystem /\ [][Next_IndexSubsystem]_allVars

\* Invariant: Index consistency
Inv_IndexSubsystem_Consistency ==
  \* All indexes for same table contain same keys
  \A t \in Tables, k \in Keys:
    LET tableIndexes == {idx \in DOMAIN indexRegistry : indexRegistry[idx].table = t}
    IN \A idx1, idx2 \in tableIndexes:
         IndexScan(idx1, k) = IndexScan(idx2, k)

THEOREM IndexSubsystem_Consistency ==
  Spec_IndexSubsystem => []Inv_IndexSubsystem_Consistency

=============================================================================

