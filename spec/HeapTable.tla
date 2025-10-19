------------------------------ MODULE HeapTable ------------------------------
(*
  ColibrìDB Heap Table Specification (Slotted Pages)
  
  Key Properties:
  - Slot Consistency: Slots non-overlapping and within page bounds
  - Free Space Validity: Free space pointers consistent
  - Page Checksum: All pages have valid checksums
  
  Author: ColibrìDB Team
  Date: 2025-10-18
*)

EXTENDS CORE, DISK_FORMAT, Naturals

VARIABLES
  pages,        \* [PageId -> Page]
  freeList,     \* Set of page IDs with free space
  allocatedRIDs \* Set of allocated RIDs

heapVars == <<pages, freeList, allocatedRIDs>>

TypeOK_Heap ==
  /\ pages \in [PageIds -> Page]
  /\ freeList \subseteq PageIds
  /\ allocatedRIDs \subseteq RID

Init_Heap ==
  /\ pages = [pid \in PageIds |-> [
       header |-> [
         magic |-> PAGE_MAGIC,
         pageId |-> pid,
         pageLSN |-> 0,
         freeStart |-> 32,  \* After header
         freeEnd |-> PAGE_SIZE,
         slotCount |-> 0,
         checksum |-> 0
       ],
       slots |-> <<>>,
       data |-> <<>>
     ]]
  /\ freeList = PageIds
  /\ allocatedRIDs = {}

InsertRow(pid, row) ==
  /\ pid \in freeList
  /\ LET page == pages[pid]
         rowSize == 100  \* Simplified
         hasSpace == HasFreeSpace(page, rowSize)
     IN
       /\ hasSpace
       /\ LET slotId == page.header.slotCount + 1
              newSlot == [
                offset |-> page.header.freeEnd - rowSize,
                length |-> rowSize,
                tombstone |-> FALSE
              ]
              rid == [pageId |-> pid, slotId |-> slotId]
          IN
            /\ pages' = [pages EXCEPT ![pid].slots = Append(@, newSlot),
                                     ![pid].header.slotCount = @ + 1,
                                     ![pid].header.freeEnd = @ - rowSize]
            /\ allocatedRIDs' = allocatedRIDs \union {rid}
            /\ UNCHANGED freeList

DeleteRow(rid) ==
  /\ rid \in allocatedRIDs
  /\ LET pid == rid.pageId
         sid == rid.slotId
         page == pages[pid]
     IN
       /\ sid <= page.header.slotCount
       /\ pages' = [pages EXCEPT ![pid].slots[sid].tombstone = TRUE]
       /\ allocatedRIDs' = allocatedRIDs \ {rid}
       /\ UNCHANGED freeList

\* Invariants
Inv_Heap_SlotConsistency ==
  \A pid \in PageIds:
    SlotsNonOverlapping(pages[pid].slots)

Inv_Heap_FreeSpaceValid ==
  \A pid \in PageIds:
    /\ pages[pid].header.freeStart <= pages[pid].header.freeEnd
    /\ pages[pid].header.freeEnd <= PAGE_SIZE

Inv_Heap_PageChecksum ==
  \A pid \in PageIds:
    ValidPage(pages[pid])

Next_Heap ==
  \/ \E pid \in PageIds, row \in Row: InsertRow(pid, row)
  \/ \E rid \in allocatedRIDs: DeleteRow(rid)

Spec_Heap == Init_Heap /\ [][Next_Heap]_heapVars
=============================================================================

