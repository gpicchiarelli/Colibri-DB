----------------------------- MODULE DISK_FORMAT -----------------------------
(*
  ColibrìDB On-Disk Data Format Specifications
  
  This module defines the abstract on-disk layout for pages, WAL records,
  and other persistent data structures.
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Version: 1.0.0
*)

EXTENDS CORE

(* --------------------------------------------------------------------------
   PAGE FORMAT
   -------------------------------------------------------------------------- *)

\* Page size in bytes (implementation: 8192)
\* For TLA+, we abstract this to a constant
CONSTANT PAGE_SIZE

\* Valid page
\* A page is valid if:
\* - Magic number is correct
\* - pageLSN >= 0
\* - freeStart <= freeEnd <= PAGE_SIZE
\* - slotCount matches actual slots
ValidPage(page) ==
  /\ page.header.magic = PAGE_MAGIC
  /\ page.header.pageLSN \in LSN
  /\ page.header.freeStart <= page.header.freeEnd
  /\ page.header.freeEnd <= PAGE_SIZE
  /\ page.header.slotCount = Len(page.slots)

\* Page has enough free space for a record of given size
HasFreeSpace(page, size) ==
  page.header.freeEnd - page.header.freeStart >= size

\* Compute page checksum (abstracted)
\* In implementation: CRC32 over entire page except checksum field
PageChecksum(page) == 42  \* Abstract checksum

\* Verify page checksum
VerifyPageChecksum(page) ==
  page.header.checksum = PageChecksum(page)

(* --------------------------------------------------------------------------
   SLOT DIRECTORY FORMAT
   -------------------------------------------------------------------------- *)

\* A slot is valid if offset and length are within page bounds
ValidSlot(slot, pageSize) ==
  /\ slot.offset >= 0
  /\ slot.offset + slot.length <= pageSize
  /\ slot.length >= 0

\* All slots in a page are non-overlapping
SlotsNonOverlapping(slots) ==
  \A i, j \in DOMAIN slots:
    i # j =>
      \/ slots[i].offset + slots[i].length <= slots[j].offset
      \/ slots[j].offset + slots[j].length <= slots[i].offset

(* --------------------------------------------------------------------------
   WAL RECORD FORMAT
   -------------------------------------------------------------------------- *)

\* WAL file header
\* Magic: 'CBDW' (0x43424457)
\* Version: 2
WAL_MAGIC == "CBDW"
WAL_VERSION == 2

WALFileHeader == [
  magic: {WAL_MAGIC},
  version: {WAL_VERSION}
]

\* WAL record header (common to all record types)
\* CRC32 | type | LSN | prevLSN | pageId | length | payload
WALRecordHeader == [
  crc32: Nat,          \* CRC32 checksum
  type: WALRecordKind, \* Record type
  lsn: LSN,            \* Log sequence number
  prevLSN: LSN,        \* Previous LSN for this transaction
  pageId: PageId,      \* Page affected by this record
  length: Nat          \* Payload length
]

\* Full WAL record with payload
WALRecordWithPayload == [
  header: WALRecordHeader,
  payload: Seq(Nat)  \* Binary payload
]

\* Valid WAL record
ValidWALRecord(record) ==
  /\ record.header.lsn \in LSN
  /\ record.header.prevLSN \in LSN \union {0}
  /\ record.header.pageId \in PageId \union {0}
  /\ record.header.length = Len(record.payload)
  /\ record.header.crc32 = WALRecordChecksum(record)

\* Compute WAL record checksum (abstracted)
\* In implementation: CRC32 over header + payload
WALRecordChecksum(record) == 42  \* Abstract checksum

(* --------------------------------------------------------------------------
   CHECKPOINT FORMAT
   -------------------------------------------------------------------------- *)

\* Checkpoint record contains:
\* - LSN of checkpoint
\* - Dirty Page Table: pageId -> recLSN (first LSN that dirtied the page)
\* - Active Transaction Table: txId -> lastLSN
CheckpointData == [
  checkpointLSN: LSN,
  dirtyPageTable: [PageId -> LSN],
  activeTransactionTable: [TxId -> LSN]
]

\* Valid checkpoint
ValidCheckpoint(checkpoint) ==
  /\ checkpoint.checkpointLSN \in LSN
  /\ \A pid \in DOMAIN checkpoint.dirtyPageTable:
       checkpoint.dirtyPageTable[pid] \in LSN
  /\ \A tid \in DOMAIN checkpoint.activeTransactionTable:
       checkpoint.activeTransactionTable[tid] \in LSN

(* --------------------------------------------------------------------------
   INDEX NODE FORMAT (B+Tree)
   -------------------------------------------------------------------------- *)

\* B+Tree internal node
\* Contains keys and child pointers
BTreeInternalNode == [
  pageId: PageId,
  pageLSN: LSN,
  keys: Seq(Value),
  children: Seq(PageId),  \* children[i] <= keys[i] < children[i+1]
  parent: PageId \union {0}
]

\* B+Tree leaf node
\* Contains keys and record pointers (RIDs)
BTreeLeafNode == [
  pageId: PageId,
  pageLSN: LSN,
  keys: Seq(Value),
  rids: Seq(Seq(RID)),  \* Each key can map to multiple RIDs
  nextLeaf: PageId \union {0},  \* For range scans
  parent: PageId \union {0}
]

\* Valid B+Tree internal node
ValidBTreeInternal(node) ==
  /\ Len(node.children) = Len(node.keys) + 1
  /\ \A i \in 1..(Len(node.keys)-1): node.keys[i] < node.keys[i+1]

\* Valid B+Tree leaf node
ValidBTreeLeaf(node) ==
  /\ Len(node.keys) = Len(node.rids)
  /\ \A i \in 1..(Len(node.keys)-1): node.keys[i] < node.keys[i+1]

(* --------------------------------------------------------------------------
   INVARIANTS
   -------------------------------------------------------------------------- *)

\* Invariant: All pages have valid format
Inv_DISK_AllPagesValid ==
  TRUE  \* Abstract invariant, defined per module

\* Invariant: All WAL records have valid format
Inv_DISK_AllWALRecordsValid ==
  TRUE  \* Abstract invariant, defined in WAL module

\* Invariant: Checksums match for all persistent data
Inv_DISK_ChecksumsValid ==
  TRUE  \* Abstract invariant, defined per module

=============================================================================

(*
  MODEL CHECKING NOTES:
  
  - PAGE_SIZE is a constant to be defined in .cfg files
  - For model checking, use small page size (e.g., 1024)
  - Checksums are abstracted to constants to avoid expensive computation
  - Real implementation uses CRC32 acceleration
  
  USAGE:
  
  ---- MODULE SomeModule ----
  EXTENDS CORE, DISK_FORMAT
  
  VARIABLE pages
  
  WritePage(pid, page) ==
    /\ ValidPage(page)
    /\ VerifyPageChecksum(page)
    /\ pages' = [pages EXCEPT ![pid] = page]
  ====================
*)

