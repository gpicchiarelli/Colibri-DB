//
//  ReplicationManager.swift
//  ColibrìDB Replication Manager
//
//  Based on: spec/Replication.tla
//  Implements: Master-Slave replication
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Replication role
public enum ReplicationRole {
    case master
    case slave
}

/// Replication state
public enum ReplicationState {
    case disconnected
    case connecting
    case syncing
    case replicating
    case error
}

/// Replication Manager
/// Corresponds to TLA+ module: Replication.tla
public actor ReplicationManager {
    // MARK: - Configuration
    
    public struct Configuration {
        public let role: ReplicationRole
        public let masterHost: String?
        public let masterPort: Int?
        public let replicationSlots: Int
        
        public init(
            role: ReplicationRole,
            masterHost: String? = nil,
            masterPort: Int? = nil,
            replicationSlots: Int = 10
        ) {
            self.role = role
            self.masterHost = masterHost
            self.masterPort = masterPort
            self.replicationSlots = replicationSlots
        }
    }
    
    // MARK: - State
    
    private let config: Configuration
    private let wal: FileWAL
    private var state: ReplicationState = .disconnected
    private var slaves: [String: SlaveConnection] = [:]
    private var replicationLSN: LSN = 0
    
    // MARK: - Initialization
    
    public init(config: Configuration, wal: FileWAL) {
        self.config = config
        self.wal = wal
    }
    
    // MARK: - Master Operations
    
    /// Register a slave
    public func registerSlave(slaveID: String, connection: SlaveConnection) throws {
        guard config.role == .master else {
            throw DBError.internalError("Not a master")
        }
        
        guard slaves.count < config.replicationSlots else {
            throw DBError.internalError("Max replication slots reached")
        }
        
        slaves[slaveID] = connection
    }
    
    /// Replicate WAL records to slaves
    public func replicateWAL(from startLSN: LSN) async throws {
        guard config.role == .master else {
            throw DBError.internalError("Not a master")
        }
        
        // Get WAL records since startLSN
        let records = await wal.getRecordsSince(startLSN)
        
        // Send to all slaves
        for (slaveID, slave) in slaves {
            do {
                try await slave.sendRecords(records)
            } catch {
                print("Failed to replicate to slave \(slaveID): \(error)")
            }
        }
    }
    
    // MARK: - Slave Operations
    
    /// Connect to master
    public func connectToMaster() async throws {
        guard config.role == .slave else {
            throw DBError.internalError("Not a slave")
        }
        
        guard let masterHost = config.masterHost,
              let masterPort = config.masterPort else {
            throw DBError.internalError("Master host/port not configured")
        }
        
        state = .connecting
        print("Connecting to master at \(masterHost):\(masterPort)...")
        
        // Simulate connection
        state = .syncing
        
        // Get current LSN from master
        let masterLSN = await wal.getCurrentLSN()
        
        // Start replication from current LSN
        replicationLSN = masterLSN
        state = .replicating
    }
    
    /// Apply replicated WAL records
    public func applyReplicatedRecords(_ records: [ConcreteWALRecord]) async throws {
        guard config.role == .slave else {
            throw DBError.internalError("Not a slave")
        }
        
        for record in records {
            // Apply record to local WAL
            _ = try await wal.append(
                kind: record.kind,
                txID: record.txID,
                pageID: record.pageID,
                payload: record.payload
            )
            
            replicationLSN = record.lsn
        }
        
        // Flush WAL
        try await wal.flush()
    }
    
    // MARK: - Query Operations
    
    /// Get replication state
    public func getState() -> ReplicationState {
        return state
    }
    
    /// Get replication lag (for slaves)
    public func getReplicationLag() async -> LSN {
        let currentLSN = await wal.getCurrentLSN()
        return currentLSN - replicationLSN
    }
    
    /// Get slave count (for master)
    public func getSlaveCount() -> Int {
        return slaves.count
    }
}

// MARK: - Supporting Types

/// Slave connection interface
public protocol SlaveConnection: Sendable {
    func sendRecords(_ records: [ConcreteWALRecord]) async throws
}

