//
//  TransactionManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Transaction management with MVCC and concurrency control.

import Foundation
import os.log

/// Transaction manager coordinating MVCC, locking, and recovery
public final class TransactionManager {
    private let logger = Logger(subsystem: "com.colibridb.transaction", category: "manager")
    private let database: Database
    private let mvcc: MVCCManager
    private let lockManager: LockManager
    
    // Transaction state
    private var nextTID: UInt64 = 1
    private var activeTransactions: [UInt64: Transaction] = [:]
    private let transactionLock = NSLock()
    
    public init(database: Database) {
        self.database = database
        self.mvcc = MVCCManager()
        self.lockManager = LockManager(defaultTimeout: 30.0)
    }
    
    /// Begins a new transaction
    public func begin(isolationLevel: IsolationLevel = .readCommitted) -> UInt64 {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        
        let tid = nextTID
        nextTID += 1
        
        let transaction = Transaction(
            id: tid,
            isolationLevel: isolationLevel,
            status: .active,
            startTime: Date(),
            lastActivity: Date()
        )
        
        activeTransactions[tid] = transaction
        mvcc.begin(tid: tid)
        
        logger.info("Transaction \(tid) started with isolation level: \(isolationLevel.rawValue)")
        return tid
    }
    
    /// Commits a transaction
    public func commit(tid: UInt64) throws {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        
        guard var transaction = activeTransactions[tid] else {
            throw TransactionError.transactionNotFound(tid)
        }
        
        guard transaction.status == .active else {
            throw TransactionError.transactionNotActive(tid)
        }
        
        logger.info("Committing transaction \(tid)")
        
        // Use database's 2PC implementation
        try database.prepareTransaction(tid)
        try database.commitPrepared(tid)
        
        // Update transaction status
        transaction.status = .committed
        transaction.endTime = Date()
        
        // Update the transaction in the dictionary
        activeTransactions[tid] = transaction
        
        // Remove from active transactions
        activeTransactions.removeValue(forKey: tid)
        
        logger.info("Transaction \(tid) committed successfully")
    }
    
    /// Rolls back a transaction
    public func rollback(tid: UInt64) throws {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        
        guard var transaction = activeTransactions[tid] else {
            throw TransactionError.transactionNotFound(tid)
        }
        
        guard transaction.status == .active else {
            throw TransactionError.transactionNotActive(tid)
        }
        
        logger.info("Rolling back transaction \(tid)")
        
        // Use database's rollback implementation
        try database.rollback(tid)
        
        // Update transaction status
        transaction.status = .aborted
        transaction.endTime = Date()
        
        // Update the transaction in the dictionary
        activeTransactions[tid] = transaction
        
        // Remove from active transactions
        activeTransactions.removeValue(forKey: tid)
        
        logger.info("Transaction \(tid) rolled back successfully")
    }
    
    /// Gets transaction information
    public func getTransaction(tid: UInt64) -> Transaction? {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        return activeTransactions[tid]
    }
    
    /// Gets all active transactions
    public func getActiveTransactions() -> [Transaction] {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        return Array(activeTransactions.values)
    }
    
    /// Checks if a transaction is active
    public func isActive(tid: UInt64) -> Bool {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        return activeTransactions[tid]?.status == .active
    }
    
    // MVCC operations are handled directly by the database
    
    /// Gets transaction statistics
    public func getStatistics() -> TransactionStatistics {
        transactionLock.lock()
        defer { transactionLock.unlock() }
        
        let activeCount = activeTransactions.count
        let totalStarted = nextTID - 1
        
        return TransactionStatistics(
            activeTransactions: activeCount,
            totalTransactions: totalStarted,
            nextTransactionId: nextTID
        )
    }
}

/// Transaction representation
public struct Transaction {
    public let id: UInt64
    public let isolationLevel: IsolationLevel
    public var status: TransactionStatus
    public let startTime: Date
    public var endTime: Date?
    public var lastActivity: Date
    
    public init(id: UInt64, isolationLevel: IsolationLevel, status: TransactionStatus, startTime: Date, lastActivity: Date) {
        self.id = id
        self.isolationLevel = isolationLevel
        self.status = status
        self.startTime = startTime
        self.lastActivity = lastActivity
    }
    
    public var duration: TimeInterval? {
        guard let endTime = endTime else { return nil }
        return endTime.timeIntervalSince(startTime)
    }
    
    public var isActive: Bool {
        return status == .active
    }
}

/// Transaction status
public enum TransactionStatus: String, Codable {
    case active
    case committed
    case aborted
    case prepared
}

/// Transaction statistics
public struct TransactionStatistics {
    public let activeTransactions: Int
    public let totalTransactions: UInt64
    public let nextTransactionId: UInt64
    
    public init(activeTransactions: Int, totalTransactions: UInt64, nextTransactionId: UInt64) {
        self.activeTransactions = activeTransactions
        self.totalTransactions = totalTransactions
        self.nextTransactionId = nextTransactionId
    }
}

/// Transaction errors
public enum TransactionError: Error, LocalizedError {
    case transactionNotFound(UInt64)
    case transactionNotActive(UInt64)
    case transactionAlreadyCommitted(UInt64)
    case transactionAlreadyAborted(UInt64)
    case deadlockDetected([UInt64])
    case lockTimeout(String)
    case isolationLevelViolation(IsolationLevel)
    case concurrentModification(String)
    
    public var errorDescription: String? {
        switch self {
        case .transactionNotFound(let tid):
            return "Transaction \(tid) not found"
        case .transactionNotActive(let tid):
            return "Transaction \(tid) is not active"
        case .transactionAlreadyCommitted(let tid):
            return "Transaction \(tid) is already committed"
        case .transactionAlreadyAborted(let tid):
            return "Transaction \(tid) is already aborted"
        case .deadlockDetected(let tids):
            return "Deadlock detected between transactions: \(tids)"
        case .lockTimeout(let resource):
            return "Lock timeout for resource: \(resource)"
        case .isolationLevelViolation(let level):
            return "Isolation level violation: \(level)"
        case .concurrentModification(let resource):
            return "Concurrent modification detected for resource: \(resource)"
        }
    }
}

/// Transaction context for operations
public struct TransactionContext {
    public let tid: UInt64
    public let isolationLevel: IsolationLevel
    public let snapshot: MVCCManager.Snapshot
    public let timeout: TimeInterval?
    
    public init(tid: UInt64, isolationLevel: IsolationLevel, snapshot: MVCCManager.Snapshot, timeout: TimeInterval? = nil) {
        self.tid = tid
        self.isolationLevel = isolationLevel
        self.snapshot = snapshot
        self.timeout = timeout
    }
}

// IsolationLevel is defined in Isolation.swift

/// Transaction timeout handler
public final class TransactionTimeoutHandler {
    private let transactionManager: TransactionManager
    private let timeout: TimeInterval
    private var timer: Timer?
    
    public init(transactionManager: TransactionManager, timeout: TimeInterval = 300) {
        self.transactionManager = transactionManager
        self.timeout = timeout
    }
    
    public func start() {
        timer = Timer.scheduledTimer(withTimeInterval: 10.0, repeats: true) { @Sendable [weak self] _ in
            self?.checkTimeouts()
        }
    }
    
    public func stop() {
        timer?.invalidate()
        timer = nil
    }
    
    private func checkTimeouts() {
        let activeTransactions = transactionManager.getActiveTransactions()
        let now = Date()
        
        for transaction in activeTransactions {
            if now.timeIntervalSince(transaction.lastActivity) > timeout {
                // Rollback timed out transaction
                try? transactionManager.rollback(tid: transaction.id)
            }
        }
    }
}

/// Transaction recovery manager
public final class TransactionRecoveryManager {
    private let logger = Logger(subsystem: "com.colibridb.transaction", category: "recovery")
    private let database: Database
    private let transactionManager: TransactionManager
    
    public init(database: Database, transactionManager: TransactionManager) {
        self.database = database
        self.transactionManager = transactionManager
    }
    
    /// Recovers from a crash
    public func recover() throws {
        logger.info("Starting transaction recovery")
        
        // Get all prepared transactions
        let preparedTransactions = getPreparedTransactions()
        
        // Commit or abort prepared transactions based on WAL
        for tid in preparedTransactions {
            if try shouldCommit(tid: tid) {
                try transactionManager.commit(tid: tid)
                logger.info("Recovered transaction \(tid) - committed")
            } else {
                try transactionManager.rollback(tid: tid)
                logger.info("Recovered transaction \(tid) - aborted")
            }
        }
        
        logger.info("Transaction recovery completed")
    }
    
    /// Gets all prepared transactions
    private func getPreparedTransactions() -> [UInt64] {
        // Get prepared transactions from database
        return Array(database.preparedTransactions)
    }
    
    /// Determines if a transaction should be committed
    private func shouldCommit(tid: UInt64) throws -> Bool {
        // Check if transaction was prepared (default to commit prepared transactions)
        // In a real distributed system, this would check coordinator decision
        return database.preparedTransactions.contains(tid)
    }
}

/// Transaction monitoring
public final class TransactionMonitor {
    private let logger = Logger(subsystem: "com.colibridb.transaction", category: "monitor")
    private let transactionManager: TransactionManager
    private var statistics: [String: Any] = [:]
    private let lock = NSLock()
    
    public init(transactionManager: TransactionManager) {
        self.transactionManager = transactionManager
    }
    
    /// Records transaction start
    public func recordStart(tid: UInt64, isolationLevel: IsolationLevel) {
        lock.lock()
        defer { lock.unlock() }
        
        statistics["transactions_started"] = (statistics["transactions_started"] as? Int ?? 0) + 1
        logger.debug("Transaction \(tid) started with isolation level: \(isolationLevel.rawValue)")
    }
    
    /// Records transaction commit
    public func recordCommit(tid: UInt64, duration: TimeInterval) {
        lock.lock()
        defer { lock.unlock() }
        
        statistics["transactions_committed"] = (statistics["transactions_committed"] as? Int ?? 0) + 1
        statistics["total_commit_duration"] = (statistics["total_commit_duration"] as? TimeInterval ?? 0) + duration
        logger.debug("Transaction \(tid) committed in \(duration)s")
    }
    
    /// Records transaction rollback
    public func recordRollback(tid: UInt64, duration: TimeInterval) {
        lock.lock()
        defer { lock.unlock() }
        
        statistics["transactions_rolled_back"] = (statistics["transactions_rolled_back"] as? Int ?? 0) + 1
        statistics["total_rollback_duration"] = (statistics["total_rollback_duration"] as? TimeInterval ?? 0) + duration
        logger.debug("Transaction \(tid) rolled back in \(duration)s")
    }
    
    /// Gets current statistics
    public func getStatistics() -> [String: Any] {
        lock.lock()
        defer { lock.unlock() }
        return statistics
    }
    
    /// Resets statistics
    public func resetStatistics() {
        lock.lock()
        defer { lock.unlock() }
        statistics.removeAll()
    }
}
