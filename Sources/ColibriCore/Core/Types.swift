//
//  Types.swift
//  ColibrìDB Core Types
//
//  Based on: spec/CORE.tla
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Basic Types

/// Log Sequence Number - monotonically increasing identifier for WAL records
/// Corresponds to TLA+: LSN == Nat
public typealias LSN = UInt64

/// Page Identifier - unique identifier for database pages
/// Corresponds to TLA+: PageId == Nat
public typealias PageID = UInt64

/// Transaction Identifier - unique identifier for transactions
/// Corresponds to TLA+: TxId == Nat
public typealias TxID = UInt64

/// Timestamp - logical or physical timestamp for MVCC
/// Corresponds to TLA+: Timestamp == Nat
public typealias Timestamp = UInt64

// MARK: - Record Identifier

/// Record Identifier - points to a tuple location in a page
/// Corresponds to TLA+: RID == [pageId: PageId, slotId: Nat]
public struct RID: Hashable, Codable, Sendable {
    public let pageID: PageID
    public let slotID: UInt32
    
    public init(pageID: PageID, slotID: UInt32) {
        self.pageID = pageID
        self.slotID = slotID
    }
}

// MARK: - Database Values

/// Value types supported by the database
/// Corresponds to TLA+: ValueType
public enum ValueType: String, Codable, Sendable {
    case int
    case double
    case bool
    case string
    case null
    case decimal
    case date
    case bytes
}

/// Database value with type and data
/// Corresponds to TLA+: Value == [type: ValueType, val: ...]
public enum Value: Hashable, Codable, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    case decimal(Decimal)
    case date(Date)
    case bytes(Data)
    
    public var type: ValueType {
        switch self {
        case .int: return .int
        case .double: return .double
        case .bool: return .bool
        case .string: return .string
        case .null: return .null
        case .decimal: return .decimal
        case .date: return .date
        case .bytes: return .bytes
        }
    }
    
    public var isNull: Bool {
        if case .null = self { return true }
        return false
    }
}

/// A row is a mapping from column names to values
/// Corresponds to TLA+: Row == [DOMAIN -> Value]
public typealias Row = [String: Value]

// MARK: - Transaction States

/// Transaction status
/// Corresponds to TLA+: TxStatus == {"active", "prepared", "committed", "aborted"}
public enum TransactionStatus: String, Codable, Sendable {
    case active
    case prepared
    case committed
    case aborted
}

/// Isolation levels for transactions
/// Corresponds to TLA+: IsolationLevel
public enum IsolationLevel: String, Codable, Sendable {
    case readUncommitted
    case readCommitted
    case repeatableRead
    case serializable
}

// MARK: - Lock Modes

/// Lock modes for concurrency control
/// Corresponds to TLA+: CoreLockMode == {"S", "X"}
public enum CoreCoreLockMode: String, Codable, Sendable {
    case shared = "S"
    case exclusive = "X"
    case intentShared = "IS"
    case intentExclusive = "IX"
    case sharedIntentExclusive = "SIX"
    
    /// Check if two lock modes are compatible
    /// Corresponds to TLA+: LockCompatible(m1, m2)
    public func isCompatible(with other: CoreLockMode) -> Bool {
        switch (self, other) {
        case (.shared, .shared),
             (.shared, .intentShared),
             (.intentShared, .shared),
             (.intentShared, .intentShared),
             (.intentShared, .intentExclusive):
            return true
        default:
            return false
        }
    }
    
    /// Full compatibility matrix (IBM DB2/PostgreSQL style)
    public static func areCompatible(_ m1: CoreLockMode, _ m2: CoreLockMode) -> Bool {
        let matrix: [CoreLockMode: [CoreLockMode: Bool]] = [
            .intentShared: [
                .intentShared: true,
                .intentExclusive: true,
                .shared: true,
                .sharedIntentExclusive: true,
                .exclusive: false
            ],
            .intentExclusive: [
                .intentShared: true,
                .intentExclusive: true,
                .shared: false,
                .sharedIntentExclusive: false,
                .exclusive: false
            ],
            .shared: [
                .intentShared: true,
                .intentExclusive: false,
                .shared: true,
                .sharedIntentExclusive: false,
                .exclusive: false
            ],
            .sharedIntentExclusive: [
                .intentShared: true,
                .intentExclusive: false,
                .shared: false,
                .sharedIntentExclusive: false,
                .exclusive: false
            ],
            .exclusive: [
                .intentShared: false,
                .intentExclusive: false,
                .shared: false,
                .sharedIntentExclusive: false,
                .exclusive: false
            ]
        ]
        
        return matrix[m1]?[m2] ?? false
    }
}

// MARK: - WAL Record Types

/// WAL record kinds
/// Corresponds to TLA+: WALRecordKind
public enum WALRecordKind: String, Codable, Sendable {
    case begin
    case commit
    case abort
    case heapInsert
    case heapUpdate
    case heapDelete
    case indexInsert
    case indexDelete
    case checkpoint
    case clr  // Compensation Log Record (for undo)
}

/// Abstract WAL record structure
/// Corresponds to TLA+: WALRecord
/// Based on ARIES paper (Mohan et al., 1992) - Figure 3
public protocol WALRecord: Codable, Sendable {
    var lsn: LSN { get }
    var prevLSN: LSN { get }
    var kind: WALRecordKind { get }
    var txID: TxID { get }
    var pageID: PageID { get }
    var undoNextLSN: LSN { get }  // For CLR records
}

// MARK: - Page Structure

/// Page header magic number
/// Corresponds to TLA+: PAGE_MAGIC == 0x434F4C49 ('COLI')
public let PAGE_MAGIC: UInt32 = 0x434F4C49

/// Page size in bytes
public let PAGE_SIZE: Int = 8192

/// Page header structure
/// Corresponds to TLA+: PageHeader
public struct PageHeader: Codable, Sendable {
    public var magic: UInt32
    public var pageID: PageID
    public var pageLSN: LSN
    public var freeStart: UInt16
    public var freeEnd: UInt16
    public var slotCount: UInt16
    public var checksum: UInt32
    
    public init(pageID: PageID, pageLSN: LSN = 0) {
        self.magic = PAGE_MAGIC
        self.pageID = pageID
        self.pageLSN = pageLSN
        self.freeStart = UInt16(MemoryLayout<PageHeader>.size)
        self.freeEnd = UInt16(PAGE_SIZE)
        self.slotCount = 0
        self.checksum = 0
    }
    
    public var isValid: Bool {
        return magic == PAGE_MAGIC &&
               freeStart <= freeEnd &&
               freeEnd <= PAGE_SIZE
    }
}

/// Page slot structure
/// Corresponds to TLA+: PageSlot
public struct PageSlot: Codable, Sendable {
    public var offset: UInt16
    public var length: UInt16
    public var tombstone: Bool
    
    public init(offset: UInt16, length: UInt16, tombstone: Bool = false) {
        self.offset = offset
        self.length = length
        self.tombstone = tombstone
    }
}

/// Abstract page representation
/// Corresponds to TLA+: Page
public struct Page: Sendable {
    public var header: PageHeader
    public var slots: [PageSlot]
    public var data: Data
    
    public init(pageID: PageID) {
        self.header = PageHeader(pageID: pageID)
        self.slots = []
        self.data = Data(count: PAGE_SIZE)
    }
}

// MARK: - Error Model

/// Error types that can occur in the system
/// Corresponds to TLA+: ErrorType
public enum DBError: Error, Sendable {
    case deadlock
    case timeout
    case notFound
    case duplicate
    case corruption
    case diskFull
    case outOfMemory
    case crash
    case invalidData
    case lockTimeout
    case serializationFailure
    case foreignKeyViolation
    case checkConstraintViolation
    case uniqueViolation
    case notNullViolation
    case ioError(String)
    case internalError(String)
}

// MARK: - Result Type

/// Result type for operations
/// Corresponds to TLA+: Result(T) == [ok: BOOLEAN, value: T \union ErrorType]
public typealias DBResult<T> = Result<T, DBError>

// MARK: - Utility Extensions

extension Result where Failure == DBError {
    public var isOk: Bool {
        if case .success = self { return true }
        return false
    }
    
    public var isErr: Bool {
        if case .failure = self { return true }
        return false
    }
}

// MARK: - Constants for Model Checking

/// Maximum transaction ID (for testing/model checking)
public let MAX_TX: TxID = 1000

/// Maximum LSN value (for testing/model checking)
public let MAX_LSN: LSN = UInt64.max

/// Maximum number of pages (for testing/model checking)
public let MAX_PAGES: PageID = 10000

