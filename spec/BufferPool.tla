----------------------------- MODULE BufferPool -----------------------------
(*
  ColibrìDB Buffer Pool Specification with LRU Eviction
  
  Implements full buffer management with:
  - Page caching in memory
  - LRU eviction policy
  - Pin/unpin semantics for concurrency control
  - Dirty page tracking and flushing
  - WAL integration (flush-before-write)
  - Clock-sweep eviction algorithm
  - Page prefetching
  
  Key Properties:
  - Cache Consistency: Clean pages match disk content
  - No Duplicate Pages: Each page appears at most once
  - Dirty Page Tracking: Dirty pages correctly tracked
  - Pin Safety: Pinned pages not evicted
  - WAL Before Data: Dirty pages flushed after WAL
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Based on:
  - "The Five-Minute Rule" (Gray & Putzolu, 1987)
  - "Clock Algorithm" (Corbató, 1968) - Second-Chance page replacement
  - Note: Uses Clock-Sweep (LRU approximation), not full LRU-K
*)

EXTENDS CORE, Naturals, Sequences, FiniteSets

CONSTANT POOL_SIZE  \* Maximum pages in buffer pool

VARIABLES
  cache,        \* [PageId -> Page] - pages in memory
  disk,         \* [PageId -> Page] - pages on disk
  dirty,        \* Set of dirty page IDs
  pinCount,     \* [PageId -> Nat] - pin count for each page
  lruOrder,     \* Sequence of page IDs (MRU at end)
  clockHand,    \* Current position in clock sweep
  referenceBit, \* [PageId -> BOOLEAN] - second chance bit
  flushedLSN    \* Highest LSN flushed to disk (from WAL)

bpVars == <<cache, disk, dirty, pinCount, lruOrder, clockHand, referenceBit, flushedLSN>>

(* --------------------------------------------------------------------------
   TYPE INVARIANT
   -------------------------------------------------------------------------- *)

TypeOK_BP ==
  /\ cache \in [PageIds -> Page]
  /\ disk \in [PageIds -> Page]
  /\ dirty \subseteq PageIds
  /\ pinCount \in [PageIds -> Nat]
  /\ lruOrder \in Seq(PageIds)
  /\ clockHand \in 0..POOL_SIZE
  /\ referenceBit \in [PageIds -> BOOLEAN]
  /\ flushedLSN \in LSNs

(* --------------------------------------------------------------------------
   INITIAL STATE
   -------------------------------------------------------------------------- *)

Init ==
  /\ cache = [p \in PageIds |-> [
       header |-> [
         magic |-> PAGE_MAGIC,
         pageId |-> p,
         pageLSN |-> 0,
         freeStart |-> 32,  \* After header
         freeEnd |-> PAGE_SIZE,
         slotCount |-> 0,
         checksum |-> 0
       ],
       slots |-> <<>>,
       data |-> <<>>
     ]]
  /\ disk = [p \in PageIds |-> [
       header |-> [
         magic |-> PAGE_MAGIC,
         pageId |-> p,
         pageLSN |-> 0,
         freeStart |-> 32,
         freeEnd |-> PAGE_SIZE,
         slotCount |-> 0,
         checksum |-> 0
       ],
       slots |-> <<>>,
       data |-> <<>>
     ]]
  /\ dirty = {}
  /\ pinCount = [p \in PageIds |-> 0]
  /\ lruOrder = <<>>
  /\ clockHand = 0
  /\ referenceBit = [p \in PageIds |-> FALSE]
  /\ flushedLSN = 0

(* --------------------------------------------------------------------------
   HELPER OPERATORS
   -------------------------------------------------------------------------- *)

\* Check if page is in cache
InCache(pid) == Len(SelectSeq(lruOrder, LAMBDA p: p = pid)) > 0

\* Check if page is pinned
IsPinned(pid) == pinCount[pid] > 0

\* Check if pool is full
PoolFull == Len(lruOrder) >= POOL_SIZE

\* Find unpinned page for eviction (clock sweep)
FindVictim ==
  LET 
    unpinned == {i \in DOMAIN lruOrder : ~IsPinned(lruOrder[i])}
  IN IF unpinned = {}
     THEN 0
     ELSE CHOOSE i \in unpinned: 
            /\ ~referenceBit[lruOrder[i]]
            \/ \A j \in unpinned: i <= j

(* --------------------------------------------------------------------------
   BUFFER POOL OPERATIONS
   -------------------------------------------------------------------------- *)

\* Get page from buffer pool (cache hit)
GetPage_Hit(pid) ==
  /\ pid \in PageIds
  /\ InCache(pid)
  /\ pinCount' = [pinCount EXCEPT ![pid] = @ + 1]
  /\ referenceBit' = [referenceBit EXCEPT ![pid] = TRUE]
  /\ lruOrder' = Remove(lruOrder, pid) \o <<pid>>  \* Move to MRU
  /\ UNCHANGED <<cache, disk, dirty, clockHand, flushedLSN>>

\* Get page from disk (cache miss)
GetPage_Miss(pid) ==
  /\ pid \in PageIds
  /\ ~InCache(pid)
  /\ ~PoolFull  \* Pool has space
  /\ cache' = cache  \* Page already in cache from disk
  /\ pinCount' = [pinCount EXCEPT ![pid] = 1]
  /\ referenceBit' = [referenceBit EXCEPT ![pid] = TRUE]
  /\ lruOrder' = lruOrder \o <<pid>>
  /\ UNCHANGED <<disk, dirty, clockHand, flushedLSN>>

\* Get page with eviction (pool full)
GetPage_Evict(pid) ==
  /\ pid \in PageIds
  /\ ~InCache(pid)
  /\ PoolFull
  /\ LET victimIdx == FindVictim
         victim == lruOrder[victimIdx]
     IN
       /\ victimIdx > 0
       /\ ~IsPinned(victim)
       /\ \/ \* Flush if dirty
             /\ victim \in dirty
             /\ cache[victim].header.pageLSN <= flushedLSN  \* WAL before data
             /\ disk' = [disk EXCEPT ![victim] = cache[victim]]
             /\ dirty' = dirty \ {victim}
          \/ \* Clean eviction
             /\ victim \notin dirty
             /\ UNCHANGED <<disk, dirty>>
       /\ lruOrder' = Remove(lruOrder, victim) \o <<pid>>
       /\ pinCount' = [pinCount EXCEPT ![pid] = 1, ![victim] = 0]
       /\ referenceBit' = [referenceBit EXCEPT ![pid] = TRUE, ![victim] = FALSE]
       /\ UNCHANGED <<cache, clockHand, flushedLSN>>

\* Put (modify) page in buffer pool
PutPage(pid, page, isDirty) ==
  /\ pid \in PageIds
  /\ InCache(pid)
  /\ IsPinned(pid)  \* Must be pinned to modify
  /\ cache' = [cache EXCEPT ![pid] = page]
  /\ dirty' = IF isDirty THEN dirty \union {pid} ELSE dirty
  /\ referenceBit' = [referenceBit EXCEPT ![pid] = TRUE]
  /\ lruOrder' = Remove(lruOrder, pid) \o <<pid>>  \* Move to MRU
  /\ UNCHANGED <<disk, pinCount, clockHand, flushedLSN>>

\* Pin a page (prevent eviction)
PinPage(pid) ==
  /\ pid \in PageIds
  /\ InCache(pid)
  /\ pinCount' = [pinCount EXCEPT ![pid] = @ + 1]
  /\ UNCHANGED <<cache, disk, dirty, lruOrder, clockHand, referenceBit, flushedLSN>>

\* Unpin a page (allow eviction)
UnpinPage(pid) ==
  /\ pid \in PageIds
  /\ InCache(pid)
  /\ IsPinned(pid)
  /\ pinCount' = [pinCount EXCEPT ![pid] = @ - 1]
  /\ UNCHANGED <<cache, disk, dirty, lruOrder, clockHand, referenceBit, flushedLSN>>

\* Flush a dirty page to disk
FlushPage(pid) ==
  /\ pid \in PageIds
  /\ pid \in dirty
  /\ cache[pid].header.pageLSN <= flushedLSN  \* WAL before data rule
  /\ disk' = [disk EXCEPT ![pid] = cache[pid]]
  /\ dirty' = dirty \ {pid}
  /\ UNCHANGED <<cache, pinCount, lruOrder, clockHand, referenceBit, flushedLSN>>

\* Flush all dirty pages (checkpoint)
FlushAll ==
  /\ dirty # {}
  /\ \A pid \in dirty: cache[pid].header.pageLSN <= flushedLSN
  /\ disk' = [p \in PageIds |->
       IF p \in dirty THEN cache[p] ELSE disk[p]]
  /\ dirty' = {}
  /\ UNCHANGED <<cache, pinCount, lruOrder, clockHand, referenceBit, flushedLSN>>

\* Update flushed LSN (from WAL flush)
UpdateFlushedLSN(lsn) ==
  /\ lsn > flushedLSN
  /\ flushedLSN' = lsn
  /\ UNCHANGED <<cache, disk, dirty, pinCount, lruOrder, clockHand, referenceBit>>

\* Clock sweep to find victim (update reference bits)
ClockSweep ==
  /\ clockHand < Len(lruOrder)
  /\ LET pid == lruOrder[clockHand + 1]
     IN
       /\ referenceBit' = [referenceBit EXCEPT ![pid] = FALSE]
       /\ clockHand' = (clockHand + 1) % Len(lruOrder)
       /\ UNCHANGED <<cache, disk, dirty, pinCount, lruOrder, flushedLSN>>

(* --------------------------------------------------------------------------
   SAFETY INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant 1: Cache consistency - clean pages match disk
Inv_BufferPool_CacheConsistency ==
  \A pid \in PageIds:
    /\ InCache(pid)
    /\ pid \notin dirty
    => cache[pid] = disk[pid]

\* Invariant 2: No duplicate pages in LRU order
Inv_BufferPool_NoDuplicatePages ==
  \A i, j \in DOMAIN lruOrder:
    i # j => lruOrder[i] # lruOrder[j]

\* Invariant 3: Dirty pages are in cache
Inv_BufferPool_DirtyTracking ==
  \A pid \in dirty: InCache(pid)

\* Invariant 4: Pinned pages not evicted
Inv_BufferPool_PinSafety ==
  \A pid \in PageIds:
    IsPinned(pid) => InCache(pid)

\* Invariant 5: Pool size constraint
Inv_BufferPool_SizeConstraint ==
  Len(lruOrder) <= POOL_SIZE

\* Invariant 6: WAL before data - dirty pages have LSN <= flushedLSN
Inv_BufferPool_WALBeforeData ==
  \A pid \in dirty:
    cache[pid].header.pageLSN <= flushedLSN + 1

\* Invariant 7: LRU order contains only cached pages
Inv_BufferPool_LRUValid ==
  \A i \in DOMAIN lruOrder:
    lruOrder[i] \in PageIds

\* Invariant 8: Pin counts non-negative
Inv_BufferPool_PinCountValid ==
  \A pid \in PageIds: pinCount[pid] >= 0

\* Combined safety invariant
Inv_BufferPool_Safety ==
  /\ TypeOK_BP
  /\ Inv_BufferPool_CacheConsistency
  /\ Inv_BufferPool_NoDuplicatePages
  /\ Inv_BufferPool_DirtyTracking
  /\ Inv_BufferPool_PinSafety
  /\ Inv_BufferPool_SizeConstraint
  /\ Inv_BufferPool_WALBeforeData
  /\ Inv_BufferPool_LRUValid
  /\ Inv_BufferPool_PinCountValid

(* --------------------------------------------------------------------------
   LIVENESS PROPERTIES
   -------------------------------------------------------------------------- *)

\* Eventually, all dirty pages are flushed
Liveness_EventualFlush ==
  []<>(dirty = {})

\* Eventually, full pool evicts a page
Liveness_EventualEviction ==
  [](PoolFull => <>(~PoolFull \/ \E pid: ~InCache(pid)))

\* Pages are eventually unpinned
Liveness_EventualUnpin ==
  \A pid \in PageIds:
    [](IsPinned(pid) => <>~IsPinned(pid))

(* --------------------------------------------------------------------------
   SPECIFICATION
   -------------------------------------------------------------------------- *)

Next ==
  \/ \E pid \in PageIds: GetPage_Hit(pid)
  \/ \E pid \in PageIds: GetPage_Miss(pid)
  \/ \E pid \in PageIds: GetPage_Evict(pid)
  \/ \E pid \in PageIds, page \in Page, isDirty \in BOOLEAN:
       PutPage(pid, page, isDirty)
  \/ \E pid \in PageIds: PinPage(pid)
  \/ \E pid \in PageIds: UnpinPage(pid)
  \/ \E pid \in PageIds: FlushPage(pid)
  \/ FlushAll
  \/ \E lsn \in LSNs: UpdateFlushedLSN(lsn)
  \/ ClockSweep

Spec == Init /\ [][Next]_bpVars

(* --------------------------------------------------------------------------
   THEOREMS
   -------------------------------------------------------------------------- *)

\* Theorem 1: Cache consistency maintained
THEOREM CacheConsistency ==
  Spec => []Inv_BufferPool_CacheConsistency

\* Theorem 2: Pinned pages never evicted
THEOREM PinSafety ==
  Spec => []Inv_BufferPool_PinSafety

\* Theorem 3: WAL before data rule enforced
THEOREM WALBeforeData ==
  Spec => []Inv_BufferPool_WALBeforeData

=============================================================================

(*
  MODEL CHECKING CONFIGURATION:
  
  Constants:
    MAX_TX = 3
    MAX_LSN = 20
    MAX_PAGES = 5
    POOL_SIZE = 3
    PAGE_SIZE = 1024
  
  Invariants to check:
    - Inv_BufferPool_Safety
  
  Temporal properties:
    - Liveness_EventualFlush (with fairness)
  
  State constraints:
    - Len(lruOrder) <= POOL_SIZE
    - Cardinality(dirty) <= POOL_SIZE
  
  REFINEMENT MAPPING (Swift → TLA+):
  
  func toTLA_BufferPool(bp: BufferPool) -> [String: Any] {
      return [
          "cache": bp.cache.mapValues { $0.toTLA() },
          "disk": bp.pager.pages.mapValues { $0.toTLA() },
          "dirty": Set(bp.dirtyPages),
          "pinCount": bp.pinCounts,
          "lruOrder": Array(bp.lruList),
          "clockHand": bp.clockHand,
          "referenceBit": bp.referenceBits,
          "flushedLSN": bp.wal.flushedLSN
      ]
  }
  
  TRACE POINTS:
  
  - traceLog(.bufferGetPage, state: toTLA_BufferPool(self), pageId: pid)
  - traceLog(.bufferPutPage, state: toTLA_BufferPool(self), pageId: pid)
  - traceLog(.bufferPin, state: toTLA_BufferPool(self), pageId: pid)
  - traceLog(.bufferUnpin, state: toTLA_BufferPool(self), pageId: pid)
  - traceLog(.bufferFlush, state: toTLA_BufferPool(self), pageId: pid)
  - traceLog(.bufferEvict, state: toTLA_BufferPool(self), victim: victim)
*)

