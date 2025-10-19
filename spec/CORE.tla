-------------------------------- MODULE CORE --------------------------------
(*
  ColibrìDB Core Types and Definitions
  
  This module defines common types, constants, and utility operators used
  by all other TLA+ specifications in ColibrìDB.
  
  Author: ColibrìDB Team
  Date: 2025-10-18
  Version: 1.0.0
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* --------------------------------------------------------------------------
   BASIC TYPES
   -------------------------------------------------------------------------- *)

\* Log Sequence Number (LSN) - monotonically increasing identifier for WAL records
\* In implementation: UInt64
LSN == Nat

\* Page Identifier - unique identifier for database pages
\* In implementation: UInt64 (PageID typealias)
PageId == Nat

\* Transaction Identifier - unique identifier for transactions
\* In implementation: UInt64
TxId == Nat

\* Timestamp - logical or physical timestamp for MVCC
\* In implementation: UInt64 or Date
Timestamp == Nat

\* Record Identifier (pageId, slotId) - points to a tuple location
\* In implementation: RID struct
RID == [pageId: PageId, slotId: Nat]

(* --------------------------------------------------------------------------
   DATABASE VALUES
   -------------------------------------------------------------------------- *)

\* Simple value types for database rows
\* In implementation: enum Value (int, double, bool, string, null, decimal, date)
ValueType == {"int", "double", "bool", "string", "null"}

\* A database value is a tuple of (type, value)
\* For model checking, we abstract values to small integers/strings
Value == [type: ValueType, val: -10..10] \union {[type |-> "null"]}

\* A row is a function from column names to values
\* In implementation: Row = [String: Value]
\* For TLA+, we model rows abstractly as records
Row == [DOMAIN -> Value]  \* Abstract representation

(* --------------------------------------------------------------------------
   TRANSACTION STATES
   -------------------------------------------------------------------------- *)

\* Transaction status
\* In implementation: MVCC.Status enum (inProgress, committed, aborted)
TxStatus == {"active", "prepared", "committed", "aborted"}

\* Isolation levels
\* In implementation: IsolationLevel enum
IsolationLevel == {"readUncommitted", "readCommitted", "repeatableRead", "serializable"}

(* --------------------------------------------------------------------------
   LOCK MODES
   -------------------------------------------------------------------------- *)

\* Lock modes for concurrency control
\* In implementation: LockMode enum (shared, exclusive)
LockMode == {"S", "X"}  \* Shared, Exclusive

\* Lock compatibility matrix
\* Two lock modes are compatible if they can be held simultaneously
\* In implementation: LockManager.canGrant()
LockCompatible(m1, m2) ==
  \/ m1 = "S" /\ m2 = "S"

(* --------------------------------------------------------------------------
   WAL RECORD TYPES
   -------------------------------------------------------------------------- *)

\* WAL record kinds
\* In implementation: WALKind enum
WALRecordKind == {
  "begin",          \* Transaction begin
  "commit",         \* Transaction commit
  "abort",          \* Transaction abort
  "heapInsert",     \* Heap insert
  "heapUpdate",     \* Heap update
  "heapDelete",     \* Heap delete
  "indexInsert",    \* Index insert
  "indexDelete",    \* Index delete
  "checkpoint",     \* Checkpoint
  "clr"            \* Compensation Log Record (for undo)
}

\* Abstract WAL record structure
\* In implementation: WALRecord protocol + specific record types
\* Based on ARIES paper (Mohan et al., 1992) - Figure 3
WALRecord == [
  lsn: LSN,
  prevLSN: LSN,        \* Previous LSN for same transaction (undo chain)
  kind: WALRecordKind,
  txId: TxId,
  pageId: PageId,
  undoNextLSN: LSN     \* For CLR records - next LSN to undo
]

(* --------------------------------------------------------------------------
   PAGE STRUCTURE
   -------------------------------------------------------------------------- *)

\* Page header magic number
PAGE_MAGIC == 0x434F4C49  \* 'COLI'

\* Page header structure
\* In implementation: PageHeader struct
PageHeader == [
  magic: {PAGE_MAGIC},
  pageId: PageId,
  pageLSN: LSN,
  freeStart: Nat,
  freeEnd: Nat,
  slotCount: Nat,
  checksum: Nat
]

\* Page slot structure
\* In implementation: PageSlot struct
PageSlot == [
  offset: Nat,
  length: Nat,
  tombstone: BOOLEAN
]

\* Abstract page representation
\* In implementation: Page struct
Page == [
  header: PageHeader,
  slots: Seq(PageSlot),
  data: Seq(Nat)  \* Byte array abstracted as sequence of naturals
]

(* --------------------------------------------------------------------------
   ERROR MODEL
   -------------------------------------------------------------------------- *)

\* Error types that can occur in the system
\* In implementation: DBError enum and various error types
ErrorType == {
  "deadlock",
  "timeout",
  "notFound",
  "duplicate",
  "corruption",
  "diskFull",
  "outOfMemory",
  "crash"
}

\* Result type: either Ok(value) or Err(error)
\* In implementation: Swift Result<T, Error>
Result(T) == [ok: BOOLEAN, value: T \union ErrorType]

Ok(v) == [ok |-> TRUE, value |-> v]
Err(e) == [ok |-> FALSE, value |-> e]

IsOk(r) == r.ok
IsErr(r) == ~r.ok

(* --------------------------------------------------------------------------
   UTILITY OPERATORS
   -------------------------------------------------------------------------- *)

\* Maximum of a set of natural numbers
Max(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Minimum of a set of natural numbers
Min(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Remove an element from a sequence
Remove(seq, elem) ==
  LET indices == {i \in DOMAIN seq : seq[i] = elem}
  IN IF indices = {} 
     THEN seq
     ELSE LET idx == CHOOSE i \in indices : TRUE
          IN [i \in 1..(Len(seq)-1) |->
               IF i < idx THEN seq[i] ELSE seq[i+1]]

\* Check if a sequence contains an element
Contains(seq, elem) == \E i \in DOMAIN seq : seq[i] = elem

\* Range of sequence indices
Range(seq) == {seq[i] : i \in DOMAIN seq}

(* --------------------------------------------------------------------------
   CONSTANTS (to be defined in .cfg files)
   -------------------------------------------------------------------------- *)

\* Maximum number of transactions (for model checking bounds)
CONSTANT MAX_TX

\* Maximum LSN value (for model checking bounds)
CONSTANT MAX_LSN

\* Maximum number of pages (for model checking bounds)
CONSTANT MAX_PAGES

\* Set of all possible transaction IDs
TxIds == 1..MAX_TX

\* Set of all possible LSNs
LSNs == 0..MAX_LSN

\* Set of all possible page IDs
PageIds == 1..MAX_PAGES

=============================================================================

(*
  MODEL CHECKING NOTES:
  
  - For model checking, we use small bounds (e.g., MAX_TX=5, MAX_LSN=100, MAX_PAGES=10)
  - Values are abstracted to small integers to keep state space manageable
  - Byte sequences are abstracted to sequences of naturals
  - Real implementations use UInt64 for LSN/PageId/TxId
  
  REFINEMENT MAPPING:
  
  Swift implementation → TLA+ abstraction:
  - FileWAL.nextLSN (UInt64) → nextLSN (Nat in 0..MAX_LSN)
  - RID(pageId, slotId) → [pageId: PageId, slotId: Nat]
  - Value (enum with associated values) → [type: ValueType, val: Int]
  - Transaction.status → TxStatus
  
  USAGE:
  
  All other TLA+ modules should EXTEND this module:
  
  ---- MODULE WAL ----
  EXTENDS CORE
  ...
  ====================
*)

