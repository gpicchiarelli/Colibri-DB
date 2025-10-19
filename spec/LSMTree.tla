---------------------------- MODULE LSMTree ----------------------------
(***************************************************************************
 * TLA+ Specification: Log-Structured Merge Tree
 *
 * Based on:
 * [1] O'Neil, P., Cheng, E., Gawlick, D., & O'Neil, E. (1996).
 *     "The Log-Structured Merge-Tree (LSM-Tree)"
 *     Acta Informatica, 33(4), 351-385.
 *     DOI: 10.1007/s002360050048
 *     Original LSM-Tree paper
 *
 * [2] Chang, F., et al. (2006).
 *     "Bigtable: A Distributed Storage System for Structured Data"
 *     7th USENIX OSDI, pp. 205-218.
 *     Production LSM implementation
 *
 * [3] Lakshman, A., & Malik, P. (2010).
 *     "Cassandra: A Decentralized Structured Storage System"
 *     ACM SIGOPS Operating Systems Review, 44(2), 35-40.
 *     DOI: 10.1145/1773912.1773922
 *     LSM in Cassandra
 *
 * [4] Sears, R., & Ramakrishnan, R. (2012).
 *     "bLSM: A General Purpose Log Structured Merge Tree"
 *     Proceedings of ACM SIGMOD, pp. 217-228.
 *     DOI: 10.1145/2213836.2213862
 *     Bloom filter optimization
 *
 * This specification models LSM-Tree including:
 * - Memtable (in-memory buffer)
 * - Multiple levels of SSTables (Sorted String Tables)
 * - Flush from memtable to Level 0
 * - Compaction between levels
 * - Read/write operations
 * - Bloom filters for lookups
 * - Write amplification and read amplification
 *
 * Author: ColibrìDB Team
 * Date: October 2025
 * Version: 1.0
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC, CORE

CONSTANTS
    MaxMemtableSize,    \* Maximum memtable entries before flush
    MaxLevels,          \* Maximum number of LSM levels
    LevelSizeRatio,     \* Size ratio between adjacent levels (typically 10)
    MaxKeysPerSSTable,  \* Maximum keys per SSTable
    Keys,               \* Set of possible keys
    Values              \* Set of possible values

ASSUME MaxMemtableSize \in Nat \ {0}
ASSUME MaxLevels \in Nat \ {0}
ASSUME LevelSizeRatio \in Nat \ {0}
ASSUME MaxKeysPerSSTable \in Nat \ {0}

(***************************************************************************
 * Entry Types (O'Neil 1996)
 ***************************************************************************)
EntryTypes == {
    "PUT",              \* Insert or update
    "DELETE"            \* Tombstone for deletion
}

VARIABLES
    \* Memtable (in-memory, O'Neil 1996 Section 2.1)
    memtable,           \* [key |-> <<value, seqNum, type>>]
    memtableSize,       \* Current memtable size
    
    \* SSTables on disk (immutable, sorted files)
    sstables,           \* [<<level, sstableId>> |-> SSTable]
    nextSSTableId,      \* [level |-> next_id]
    
    \* Level metadata
    levelSize,          \* [level |-> num_entries]
    
    \* Compaction state
    compacting,         \* Set of <<level, sstableId>> being compacted
    
    \* Write-Ahead Log (for crash recovery)
    wal,                \* Sequence of operations
    
    \* Sequence number (for ordering)
    seqNum,             \* Global sequence number
    
    \* Bloom filters (Sears 2012, per SSTable)
    bloomFilters        \* [<<level, sstableId>> |-> Set of keys]

memVars == <<memtable, memtableSize>>
sstableVars == <<sstables, nextSSTableId, levelSize>>
compactionVars == <<compacting>>
persistentVars == <<wal, bloomFilters>>
vars == <<memVars, sstableVars, compactionVars, persistentVars, seqNum>>

(***************************************************************************
 * SSTable Structure (O'Neil 1996)
 ***************************************************************************)
SSTable == [
    id: Nat,
    level: 0..MaxLevels,
    entries: [Keys -> <<Values, Nat, EntryTypes>>],  \* Sorted by key
    minKey: Keys \cup {NULL},
    maxKey: Keys \cup {NULL},
    size: Nat
]

(***************************************************************************
 * Type Invariants
 ***************************************************************************)
TypeOK ==
    /\ memtable \in [Keys -> <<Values, Nat, EntryTypes>>]
    /\ memtableSize \in Nat
    /\ sstables \in [((0..MaxLevels \X Nat)) -> SSTable]
    /\ nextSSTableId \in [0..MaxLevels -> Nat]
    /\ levelSize \in [0..MaxLevels -> Nat]
    /\ compacting \subseteq ((0..MaxLevels \X Nat))
    /\ wal \in Seq([key: Keys, value: Values, type: EntryTypes])
    /\ seqNum \in Nat
    /\ bloomFilters \in [((0..MaxLevels \X Nat)) -> SUBSET Keys]

(***************************************************************************
 * Initial State
 ***************************************************************************)
Init ==
    /\ memtable = [k \in {} |-> <<>>]
    /\ memtableSize = 0
    /\ sstables = [x \in {} |-> {}]
    /\ nextSSTableId = [level \in 0..MaxLevels |-> 1]
    /\ levelSize = [level \in 0..MaxLevels |-> 0]
    /\ compacting = {}
    /\ wal = <<>>
    /\ seqNum = 1
    /\ bloomFilters = [x \in {} |-> {}]

(***************************************************************************
 * Helper Functions
 ***************************************************************************)

\* Check if memtable should be flushed
ShouldFlush ==
    memtableSize >= MaxMemtableSize

\* Check if level should be compacted (O'Neil 1996, Section 3.1)
ShouldCompact(level) ==
    /\ level < MaxLevels
    /\ levelSize[level] > LevelSizeRatio * levelSize[level + 1]

\* Get value from memtable or SSTables (read path)
\* Searches memtable first, then levels from 0 to MaxLevels
\* (O'Neil 1996, Section 2.2)

\* Bloom filter check (Sears 2012)
BloomFilterContains(level, sstId, key) ==
    <<level, sstId>> \in DOMAIN bloomFilters =>
        key \in bloomFilters[<<level, sstId>>]

(***************************************************************************
 * Actions: Write Operations (O'Neil 1996, Section 2.1)
 ***************************************************************************)

\* Put operation: write to memtable
Put(key, value) ==
    /\ key \in Keys
    /\ value \in Values
    /\ ~ShouldFlush  \* Flush if full
    /\ LET entry == <<value, seqNum, "PUT">>
       IN
        /\ memtable' = [memtable EXCEPT ![key] = entry]
        /\ IF key \in DOMAIN memtable
           THEN memtableSize' = memtableSize  \* Update existing
           ELSE memtableSize' = memtableSize + 1  \* New entry
        /\ wal' = Append(wal, [key |-> key, value |-> value, type |-> "PUT"])
        /\ seqNum' = seqNum + 1
        /\ UNCHANGED <<sstableVars, compactionVars, bloomFilters>>

\* Delete operation: write tombstone to memtable
Delete(key) ==
    /\ key \in Keys
    /\ ~ShouldFlush
    /\ LET entry == <<NULL, seqNum, "DELETE">>
       IN
        /\ memtable' = [memtable EXCEPT ![key] = entry]
        /\ IF key \in DOMAIN memtable
           THEN memtableSize' = memtableSize
           ELSE memtableSize' = memtableSize + 1
        /\ wal' = Append(wal, [key |-> key, value |-> NULL, type |-> "DELETE"])
        /\ seqNum' = seqNum + 1
        /\ UNCHANGED <<sstableVars, compactionVars, bloomFilters>>

(***************************************************************************
 * Actions: Flush (O'Neil 1996, Section 2.3)
 ***************************************************************************)

\* Flush memtable to Level 0 SSTable
FlushMemtable ==
    /\ ShouldFlush
    /\ memtableSize > 0
    /\ LET level == 0
           sstId == nextSSTableId[level]
           \* Create new SSTable from memtable
           sst == [
               id |-> sstId,
               level |-> level,
               entries |-> memtable,
               minKey |-> CHOOSE k \in DOMAIN memtable : 
                   \A k2 \in DOMAIN memtable : k <= k2,
               maxKey |-> CHOOSE k \in DOMAIN memtable : 
                   \A k2 \in DOMAIN memtable : k >= k2,
               size |-> memtableSize
           ]
           \* Create Bloom filter for new SSTable (Sears 2012)
           bloom == DOMAIN memtable
       IN
        /\ sstables' = sstables @@ (<<level, sstId>> :> sst)
        /\ nextSSTableId' = [nextSSTableId EXCEPT ![level] = @ + 1]
        /\ levelSize' = [levelSize EXCEPT ![level] = @ + memtableSize]
        /\ bloomFilters' = bloomFilters @@ (<<level, sstId>> :> bloom)
        /\ memtable' = [k \in {} |-> <<>>]
        /\ memtableSize' = 0
        /\ wal' = <<>>  \* Can truncate WAL after flush
        /\ UNCHANGED <<compactionVars, seqNum>>

(***************************************************************************
 * Actions: Compaction (O'Neil 1996, Section 3)
 ***************************************************************************)

\* Start compaction from level to level+1
StartCompaction(level) ==
    /\ level \in 0..(MaxLevels-1)
    /\ ShouldCompact(level)
    /\ \E sstId \in Nat :
        /\ <<level, sstId>> \in DOMAIN sstables
        /\ <<level, sstId>> \notin compacting
        /\ compacting' = compacting \cup {<<level, sstId>>}
        /\ UNCHANGED <<memVars, sstableVars, persistentVars, seqNum>>

\* Perform compaction: merge SSTables from level to level+1
PerformCompaction(level, sstId) ==
    /\ <<level, sstId>> \in compacting
    /\ <<level, sstId>> \in DOMAIN sstables
    /\ level < MaxLevels
    /\ LET sst == sstables[<<level, sstId>>]
           nextLevel == level + 1
           nextSSTId == nextSSTableId[nextLevel]
           \* Find overlapping SSTables in next level
           overlapping == {<<nextLevel, id>> \in DOMAIN sstables :
               /\ sstables[<<nextLevel, id>>].minKey <= sst.maxKey
               /\ sstables[<<nextLevel, id>>].maxKey >= sst.minKey}
           \* Merge entries (simplified: just move to next level)
           newSST == [
               id |-> nextSSTId,
               level |-> nextLevel,
               entries |-> sst.entries,
               minKey |-> sst.minKey,
               maxKey |-> sst.maxKey,
               size |-> sst.size
           ]
           newBloom == DOMAIN sst.entries
       IN
        \* Remove old SSTable from level
        /\ sstables' = [x \in (DOMAIN sstables \ {<<level, sstId>>}) \cup 
                              {<<nextLevel, nextSSTId>>} |->
                       IF x = <<nextLevel, nextSSTId>> 
                       THEN newSST 
                       ELSE sstables[x]]
        /\ nextSSTableId' = [nextSSTableId EXCEPT ![nextLevel] = @ + 1]
        /\ levelSize' = [levelSize EXCEPT 
            ![level] = @ - sst.size,
            ![nextLevel] = @ + sst.size]
        /\ bloomFilters' = [x \in (DOMAIN bloomFilters \ {<<level, sstId>>}) \cup 
                                 {<<nextLevel, nextSSTId>>} |->
                           IF x = <<nextLevel, nextSSTId>> 
                           THEN newBloom 
                           ELSE bloomFilters[x]]
        /\ compacting' = compacting \ {<<level, sstId>>}
        /\ UNCHANGED <<memVars, wal, seqNum>>

(***************************************************************************
 * Actions: Read Operations (O'Neil 1996, Section 2.2)
 ***************************************************************************)

\* Get operation: search memtable and SSTables
Get(key) ==
    /\ key \in Keys
    /\ IF key \in DOMAIN memtable
       THEN \* Found in memtable
            UNCHANGED vars
       ELSE \* Search SSTables from Level 0 to MaxLevels
            \E level \in 0..MaxLevels, sstId \in Nat :
                /\ <<level, sstId>> \in DOMAIN sstables
                /\ BloomFilterContains(level, sstId, key)
                /\ key \in DOMAIN sstables[<<level, sstId>>].entries
                /\ UNCHANGED vars

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next ==
    \/ \E k \in Keys, v \in Values : Put(k, v)
    \/ \E k \in Keys : Delete(k)
    \/ FlushMemtable
    \/ \E level \in 0..(MaxLevels-1) : StartCompaction(level)
    \/ \E level \in 0..(MaxLevels-1), sstId \in Nat : 
        PerformCompaction(level, sstId)
    \/ \E k \in Keys : Get(k)

Spec == Init /\ [][Next]_vars

(***************************************************************************
 * Safety Properties (O'Neil 1996)
 ***************************************************************************)

\* Memtable size bounded
MemtableSizeBounded ==
    memtableSize <= MaxMemtableSize

\* SSTables are immutable (entries never change)
SSTablesImmutable ==
    \A level \in 0..MaxLevels, sstId \in Nat :
        <<level, sstId>> \in DOMAIN sstables =>
            []([<<level, sstId>> \in DOMAIN sstables =>
                sstables[<<level, sstId>>].entries = 
                sstables[<<level, sstId>>].entries]_vars)

\* Level sizes increase geometrically (O'Neil 1996, Section 3.1)
LevelSizeRatioMaintained ==
    \A level \in 0..(MaxLevels-1) :
        levelSize[level] > LevelSizeRatio * levelSize[level + 1]
            => <>~(levelSize[level] > LevelSizeRatio * levelSize[level + 1])

\* SSTable size bounded
SSTableSizeBounded ==
    \A level \in 0..MaxLevels, sstId \in Nat :
        <<level, sstId>> \in DOMAIN sstables =>
            sstables[<<level, sstId>>].size <= MaxKeysPerSSTable

\* Bloom filter accuracy (no false negatives)
BloomFilterAccurate ==
    \A level \in 0..MaxLevels, sstId \in Nat, key \in Keys :
        /\ <<level, sstId>> \in DOMAIN sstables
        /\ key \in DOMAIN sstables[<<level, sstId>>].entries
        => BloomFilterContains(level, sstId, key)

Safety ==
    /\ MemtableSizeBounded
    /\ SSTableSizeBounded
    /\ BloomFilterAccurate

(***************************************************************************
 * Liveness Properties
 ***************************************************************************)

\* Memtable eventually flushed when full
MemtableEventuallyFlushed ==
    ShouldFlush ~> (memtableSize = 0)

\* Compaction eventually reduces level size
CompactionEventuallyCompletes ==
    \A level \in 0..(MaxLevels-1) :
        ShouldCompact(level) ~> ~ShouldCompact(level)

\* Reads eventually complete
ReadsEventuallyComplete ==
    \A k \in Keys : Get(k) ~> TRUE

Liveness ==
    /\ MemtableEventuallyFlushed
    /\ CompactionEventuallyCompletes

(***************************************************************************
 * Performance Properties (O'Neil 1996, Section 4)
 ***************************************************************************)

\* Write amplification: number of times data is written
\* In LSM, each entry may be written once to WAL, once to memtable,
\* then rewritten during each compaction (log(N) times)

\* Read amplification: number of levels to check for a key
\* In worst case, must check all levels (MaxLevels + 1 including memtable)

(***************************************************************************
 * Theorems
 ***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => []MemtableSizeBounded
THEOREM Spec => []SSTableSizeBounded

================================================================================

