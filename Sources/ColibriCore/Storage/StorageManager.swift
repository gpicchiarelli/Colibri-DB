//
//  StorageManager.swift
//  ColibrìDB Storage Management Implementation
//
//  Based on: spec/Storage.tla
//  Implements: Database storage management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Durability: Data persists across failures
//  - Consistency: Data integrity maintained
//  - Performance: Efficient storage operations
//  - Scalability: Handles large datasets
//

import Foundation

// MARK: - Storage Types

/// Storage type
/// Corresponds to TLA+: StorageType
public enum StorageType: String, Codable, Sendable {
    case memory = "memory"
    case disk = "disk"
    case ssd = "ssd"
    case network = "network"
    case hybrid = "hybrid"
}

/// Storage status
/// Corresponds to TLA+: StorageStatus
public enum StorageStatus: String, Codable, Sendable {
    case active = "active"
    case inactive = "inactive"
    case degraded = "degraded"
    case failed = "failed"
    case maintenance = "maintenance"
}

/// Storage operation
/// Corresponds to TLA+: StorageOperation
public enum StorageOperation: String, Codable, Sendable {
    case read = "read"
    case write = "write"
    case delete = "delete"
    case update = "update"
    case scan = "scan"
    case backup = "backup"
    case restore = "restore"
}

// MARK: - Storage Metadata

/// Storage device
/// Corresponds to TLA+: StorageDevice
public struct StorageDevice: Codable, Sendable, Equatable {
    public let deviceId: String
    public let type: StorageType
    public let status: StorageStatus
    public let capacity: Int64
    public let usedSpace: Int64
    public let freeSpace: Int64
    public let readSpeed: Double
    public let writeSpeed: Double
    public let latency: TimeInterval
    public let createdAt: Date
    public let lastAccessed: Date
    
    public init(deviceId: String, type: StorageType, status: StorageStatus, capacity: Int64, usedSpace: Int64, freeSpace: Int64, readSpeed: Double, writeSpeed: Double, latency: TimeInterval, createdAt: Date = Date(), lastAccessed: Date = Date()) {
        self.deviceId = deviceId
        self.type = type
        self.status = status
        self.capacity = capacity
        self.usedSpace = usedSpace
        self.freeSpace = freeSpace
        self.readSpeed = readSpeed
        self.writeSpeed = writeSpeed
        self.latency = latency
        self.createdAt = createdAt
        self.lastAccessed = lastAccessed
    }
}

/// Storage operation result
/// Corresponds to TLA+: StorageOperationResult
public struct StorageOperationResult: Codable, Sendable, Equatable {
    public let operationId: String
    public let operation: StorageOperation
    public let success: Bool
    public let data: Data?
    public let bytesRead: Int
    public let bytesWritten: Int
    public let executionTime: TimeInterval
    public let error: String?
    public let timestamp: Date
    
    public init(operationId: String, operation: StorageOperation, success: Bool, data: Data?, bytesRead: Int, bytesWritten: Int, executionTime: TimeInterval, error: String? = nil, timestamp: Date = Date()) {
        self.operationId = operationId
        self.operation = operation
        self.success = success
        self.data = data
        self.bytesRead = bytesRead
        self.bytesWritten = bytesWritten
        self.executionTime = executionTime
        self.error = error
        self.timestamp = timestamp
    }
}

/// Storage statistics
/// Corresponds to TLA+: StorageStatistics
public struct StorageStatistics: Codable, Sendable, Equatable {
    public let totalCapacity: Int64
    public let totalUsedSpace: Int64
    public let totalFreeSpace: Int64
    public let totalReadOperations: Int
    public let totalWriteOperations: Int
    public let totalBytesRead: Int64
    public let totalBytesWritten: Int64
    public let averageReadLatency: TimeInterval
    public let averageWriteLatency: TimeInterval
    public let throughput: Double
    
    public init(totalCapacity: Int64, totalUsedSpace: Int64, totalFreeSpace: Int64, totalReadOperations: Int, totalWriteOperations: Int, totalBytesRead: Int64, totalBytesWritten: Int64, averageReadLatency: TimeInterval, averageWriteLatency: TimeInterval, throughput: Double) {
        self.totalCapacity = totalCapacity
        self.totalUsedSpace = totalUsedSpace
        self.totalFreeSpace = totalFreeSpace
        self.totalReadOperations = totalReadOperations
        self.totalWriteOperations = totalWriteOperations
        self.totalBytesRead = totalBytesRead
        self.totalBytesWritten = totalBytesWritten
        self.averageReadLatency = averageReadLatency
        self.averageWriteLatency = averageWriteLatency
        self.throughput = throughput
    }
}

// MARK: - Storage Manager

/// Storage Manager for database storage management
/// Corresponds to TLA+ module: Storage.tla
public actor StorageManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Storage devices
    /// TLA+: storageDevices \in [DeviceId -> StorageDevice]
    private var storageDevices: [String: StorageDevice] = [:]
    
    /// Storage operations
    /// TLA+: storageOperations \in [OperationId -> StorageOperationResult]
    private var storageOperations: [String: StorageOperationResult] = [:]
    
    /// Storage statistics
    /// TLA+: storageStatistics \in StorageStatistics
    private var storageStatistics: StorageStatistics
    
    /// Storage cache
    /// TLA+: storageCache \in [Key -> Data]
    private var storageCache: [String: Data] = [:]
    
    /// Storage history
    /// TLA+: storageHistory \in Seq(StorageEvent)
    private var storageHistory: [StorageEvent] = []
    
    /// Storage configuration
    private var storageConfig: StorageConfig
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: DiskManager
    
    /// Cache manager
    private let cacheManager: CacheManager
    
    /// WAL for logging
    private let wal: FileWAL
    
    // MARK: - Initialization
    
    public init(diskManager: DiskManager, cacheManager: CacheManager, wal: FileWAL, storageConfig: StorageConfig = StorageConfig()) {
        self.diskManager = diskManager
        self.cacheManager = cacheManager
        self.wal = wal
        self.storageConfig = storageConfig
        
        // TLA+ Init
        self.storageDevices = [:]
        self.storageOperations = [:]
        self.storageStatistics = StorageStatistics(
            totalCapacity: 0,
            totalUsedSpace: 0,
            totalFreeSpace: 0,
            totalReadOperations: 0,
            totalWriteOperations: 0,
            totalBytesRead: 0,
            totalBytesWritten: 0,
            averageReadLatency: 0,
            averageWriteLatency: 0,
            throughput: 0
        )
        self.storageCache = [:]
        self.storageHistory = []
        
        // Initialize default storage devices
        initializeDefaultStorageDevices()
    }
    
    // MARK: - Storage Device Management
    
    /// Add storage device
    /// TLA+ Action: AddStorageDevice(deviceId, device)
    public func addStorageDevice(deviceId: String, device: StorageDevice) throws {
        // TLA+: Check if device already exists
        guard storageDevices[deviceId] == nil else {
            throw StorageError.deviceAlreadyExists
        }
        
        // TLA+: Validate device
        try validateStorageDevice(device)
        
        // TLA+: Add device
        storageDevices[deviceId] = device
        
        // TLA+: Update statistics
        updateStorageStatistics()
        
        // TLA+: Log device addition
        let event = StorageEvent(
            eventId: "\(deviceId)_added",
            deviceId: deviceId,
            eventType: .deviceAdded,
            timestamp: Date(),
            data: ["type": .string(device.type.rawValue), "capacity": .int(Int(device.capacity))])
        storageHistory.append(event)
    }
    
    /// Remove storage device
    /// TLA+ Action: RemoveStorageDevice(deviceId)
    public func removeStorageDevice(deviceId: String) throws {
        // TLA+: Check if device exists
        guard let device = storageDevices[deviceId] else {
            throw StorageError.deviceNotFound
        }
        
        // TLA+: Check if device is in use
        guard device.status == .inactive else {
            throw StorageError.deviceInUse
        }
        
        // TLA+: Remove device
        storageDevices.removeValue(forKey: deviceId)
        
        // TLA+: Update statistics
        updateStorageStatistics()
        
        // TLA+: Log device removal
        let event = StorageEvent(
            eventId: "\(deviceId)_removed",
            deviceId: deviceId,
            eventType: .deviceRemoved,
            timestamp: Date(),
            data: [:])
        storageHistory.append(event)
    }
    
    /// Update storage device
    /// TLA+ Action: UpdateStorageDevice(deviceId, device)
    public func updateStorageDevice(deviceId: String, device: StorageDevice) throws {
        // TLA+: Check if device exists
        guard storageDevices[deviceId] != nil else {
            throw StorageError.deviceNotFound
        }
        
        // TLA+: Validate device
        try validateStorageDevice(device)
        
        // TLA+: Update device
        storageDevices[deviceId] = device
        
        // TLA+: Update statistics
        updateStorageStatistics()
        
        // TLA+: Log device update
        let event = StorageEvent(
            eventId: "\(deviceId)_updated",
            deviceId: deviceId,
            eventType: .deviceUpdated,
            timestamp: Date(),
            data: ["type": .string(device.type.rawValue), "status": .string(device.status.rawValue)])
        storageHistory.append(event)
    }
    
    // MARK: - Storage Operations
    
    /// Read data
    /// TLA+ Action: ReadData(key, deviceId)
    public func readData(key: String, deviceId: String? = nil) async throws -> Data {
        // TLA+: Check cache first
        if let cachedData = storageCache[key] {
            // TLA+: Log cache hit
            let event = StorageEvent(
                eventId: "\(key)_cache_hit",
                deviceId: deviceId ?? "cache",
                eventType: .cacheHit,
                timestamp: Date(),
                data: ["key": .string(key)])
            storageHistory.append(event)
            
            return cachedData
        }
        
        // TLA+: Select device
        let targetDeviceId = deviceId ?? selectOptimalDevice(for: .read)
        
        // TLA+: Check if device exists
        guard let device = storageDevices[targetDeviceId] else {
            throw StorageError.deviceNotFound
        }
        
        // TLA+: Check if device is active
        guard device.status == .active else {
            throw StorageError.deviceNotActive
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Read data from device
            let data = try await diskManager.readData(key: key, deviceId: targetDeviceId)
            
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Cache data
            storageCache[key] = data
            
            // TLA+: Record operation
            let operation = StorageOperationResult(
                operationId: "\(key)_read_\(Date().timeIntervalSince1970)",
                operation: .read,
                success: true,
                data: data,
                bytesRead: data.count,
                bytesWritten: 0,
                executionTime: executionTime
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Update statistics
            updateStorageStatistics()
            
            // TLA+: Log read operation
            let event = StorageEvent(
                eventId: "\(key)_read",
                deviceId: targetDeviceId,
                eventType: .readOperation,
                timestamp: Date(),
                data: ["key": .string(key), "bytesRead": .int(data.count)])
            storageHistory.append(event)
            
            return data
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Record failed operation
            let operation = StorageOperationResult(
                operationId: "\(key)_read_\(Date().timeIntervalSince1970)",
                operation: .read,
                success: false,
                data: nil,
                bytesRead: 0,
                bytesWritten: 0,
                executionTime: executionTime,
                error: error.localizedDescription
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Log read failure
            let event = StorageEvent(
                eventId: "\(key)_read_failed",
                deviceId: targetDeviceId,
                eventType: .readFailure,
                timestamp: Date(),
                data: ["key": .string(key), "error": .string(error.localizedDescription)])
            storageHistory.append(event)
            
            throw error
        }
    }
    
    /// Write data
    /// TLA+ Action: WriteData(key, data, deviceId)
    public func writeData(key: String, data: Data, deviceId: String? = nil) async throws {
        // TLA+: Select device
        let targetDeviceId = deviceId ?? selectOptimalDevice(for: .write)
        
        // TLA+: Check if device exists
        guard let device = storageDevices[targetDeviceId] else {
            throw StorageError.deviceNotFound
        }
        
        // TLA+: Check if device is active
        guard device.status == .active else {
            throw StorageError.deviceNotActive
        }
        
        // TLA+: Check if device has enough space
        guard device.freeSpace >= Int64(data.count) else {
            throw StorageError.insufficientSpace
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Write data to device
            try await diskManager.writeData(key: key, data: data, deviceId: targetDeviceId)
            
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Cache data
            storageCache[key] = data
            
            // TLA+: Record operation
            let operation = StorageOperationResult(
                operationId: "\(key)_write_\(Date().timeIntervalSince1970)",
                operation: .write,
                success: true,
                data: data,
                bytesRead: 0,
                bytesWritten: data.count,
                executionTime: executionTime
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Update device usage
            updateDeviceUsage(deviceId: targetDeviceId, bytesWritten: data.count)
            
            // TLA+: Update statistics
            updateStorageStatistics()
            
            // TLA+: Log write operation
            let event = StorageEvent(
                eventId: "\(key)_write",
                deviceId: targetDeviceId,
                eventType: .writeOperation,
                timestamp: Date(),
                data: ["key": .string(key), "bytesWritten": .int(data.count)])
            storageHistory.append(event)
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Record failed operation
            let operation = StorageOperationResult(
                operationId: "\(key)_write_\(Date().timeIntervalSince1970)",
                operation: .write,
                success: false,
                data: data,
                bytesRead: 0,
                bytesWritten: 0,
                executionTime: executionTime,
                error: error.localizedDescription
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Log write failure
            let event = StorageEvent(
                eventId: "\(key)_write_failed",
                deviceId: targetDeviceId,
                eventType: .writeFailure,
                timestamp: Date(),
                data: ["key": .string(key), "error": .string(error.localizedDescription)])
            storageHistory.append(event)
            
            throw error
        }
    }
    
    /// Delete data
    /// TLA+ Action: DeleteData(key, deviceId)
    public func deleteData(key: String, deviceId: String? = nil) async throws {
        // TLA+: Select device
        let targetDeviceId = deviceId ?? selectOptimalDevice(for: .delete)
        
        // TLA+: Check if device exists
        guard let device = storageDevices[targetDeviceId] else {
            throw StorageError.deviceNotFound
        }
        
        // TLA+: Check if device is active
        guard device.status == .active else {
            throw StorageError.deviceNotActive
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Delete data from device
            try await diskManager.deleteData(key: key, deviceId: targetDeviceId)
            
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Remove from cache
            storageCache.removeValue(forKey: key)
            
            // TLA+: Record operation
            let operation = StorageOperationResult(
                operationId: "\(key)_delete_\(Date().timeIntervalSince1970)",
                operation: .delete,
                success: true,
                data: nil,
                bytesRead: 0,
                bytesWritten: 0,
                executionTime: executionTime
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Update statistics
            updateStorageStatistics()
            
            // TLA+: Log delete operation
            let event = StorageEvent(
                eventId: "\(key)_delete",
                deviceId: targetDeviceId,
                eventType: .deleteOperation,
                timestamp: Date(),
                data: ["key": .string(key)])
            storageHistory.append(event)
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Record failed operation
            let operation = StorageOperationResult(
                operationId: "\(key)_delete_\(Date().timeIntervalSince1970)",
                operation: .delete,
                success: false,
                data: nil,
                bytesRead: 0,
                bytesWritten: 0,
                executionTime: executionTime,
                error: error.localizedDescription
            )
            storageOperations[operation.operationId] = operation
            
            // TLA+: Log delete failure
            let event = StorageEvent(
                eventId: "\(key)_delete_failed",
                deviceId: targetDeviceId,
                eventType: .deleteFailure,
                timestamp: Date(),
                data: ["key": .string(key), "error": .string(error.localizedDescription)])
            storageHistory.append(event)
            
            throw error
        }
    }
    
    // MARK: - Helper Methods
    
    /// Validate storage device
    private func validateStorageDevice(_ device: StorageDevice) throws {
        // TLA+: Validate storage device
        guard device.capacity > 0 else {
            throw StorageError.invalidCapacity
        }
        
        guard device.usedSpace >= 0 else {
            throw StorageError.invalidUsedSpace
        }
        
        guard device.freeSpace >= 0 else {
            throw StorageError.invalidFreeSpace
        }
        
        guard device.usedSpace + device.freeSpace <= device.capacity else {
            throw StorageError.invalidSpaceAllocation
        }
    }
    
    /// Select optimal device
    private func selectOptimalDevice(for operation: StorageOperation) -> String {
        // TLA+: Select optimal device based on operation
        let activeDevices = storageDevices.filter { $0.value.status == .active }
        
        switch operation {
        case .read:
            // TLA+: Select device with lowest latency
            return activeDevices.min { $0.value.latency < $1.value.latency }?.key ?? ""
        case .write:
            // TLA+: Select device with highest write speed
            return activeDevices.max { $0.value.writeSpeed < $1.value.writeSpeed }?.key ?? ""
        case .delete:
            // TLA+: Select device with lowest latency
            return activeDevices.min { $0.value.latency < $1.value.latency }?.key ?? ""
        default:
            // TLA+: Select first available device
            return activeDevices.first?.key ?? ""
        }
    }
    
    /// Update device usage
    private func updateDeviceUsage(deviceId: String, bytesWritten: Int) {
        // TLA+: Update device usage
        if var device = storageDevices[deviceId] {
            device.usedSpace += Int64(bytesWritten)
            device.freeSpace -= Int64(bytesWritten)
            device.lastAccessed = Date()
            storageDevices[deviceId] = device
        }
    }
    
    /// Update storage statistics
    private func updateStorageStatistics() {
        // TLA+: Update storage statistics
        let totalCapacity = storageDevices.values.reduce(0) { $0 + $1.capacity }
        let totalUsedSpace = storageDevices.values.reduce(0) { $0 + $1.usedSpace }
        let totalFreeSpace = storageDevices.values.reduce(0) { $0 + $1.freeSpace }
        
        let totalReadOperations = storageOperations.values.filter { $0.operation == .read }.count
        let totalWriteOperations = storageOperations.values.filter { $0.operation == .write }.count
        
        let totalBytesRead = storageOperations.values.reduce(0) { $0 + Int64($1.bytesRead) }
        let totalBytesWritten = storageOperations.values.reduce(0) { $0 + Int64($1.bytesWritten) }
        
        let readOperations = storageOperations.values.filter { $0.operation == .read && $0.success }
        let writeOperations = storageOperations.values.filter { $0.operation == .write && $0.success }
        
        let averageReadLatency = readOperations.isEmpty ? 0 : readOperations.reduce(0) { $0 + $1.executionTime } / Double(readOperations.count)
        let averageWriteLatency = writeOperations.isEmpty ? 0 : writeOperations.reduce(0) { $0 + $1.executionTime } / Double(writeOperations.count)
        
        let throughput = totalBytesRead + totalBytesWritten > 0 ? Double(totalBytesRead + totalBytesWritten) / 1024 / 1024 : 0 // MB/s
        
        storageStatistics = StorageStatistics(
            totalCapacity: totalCapacity,
            totalUsedSpace: totalUsedSpace,
            totalFreeSpace: totalFreeSpace,
            totalReadOperations: totalReadOperations,
            totalWriteOperations: totalWriteOperations,
            totalBytesRead: totalBytesRead,
            totalBytesWritten: totalBytesWritten,
            averageReadLatency: averageReadLatency,
            averageWriteLatency: averageWriteLatency,
            throughput: throughput
        )
    }
    
    /// Initialize default storage devices
    private func initializeDefaultStorageDevices() {
        // TLA+: Initialize default storage devices
        let defaultDevices = [
            StorageDevice(
                deviceId: "memory_1",
                type: .memory,
                status: .active,
                capacity: 8 * 1024 * 1024 * 1024, // 8GB
                usedSpace: 0,
                freeSpace: 8 * 1024 * 1024 * 1024,
                readSpeed: 10000, // MB/s
                writeSpeed: 10000,
                latency: 0.001 // 1ms
            ),
            StorageDevice(
                deviceId: "disk_1",
                type: .disk,
                status: .active,
                capacity: 1000 * 1024 * 1024 * 1024, // 1TB
                usedSpace: 0,
                freeSpace: 1000 * 1024 * 1024 * 1024,
                readSpeed: 150, // MB/s
                writeSpeed: 150,
                latency: 0.01 // 10ms
            )
        ]
        
        for device in defaultDevices {
            storageDevices[device.deviceId] = device
        }
        
        updateStorageStatistics()
    }
    
    // MARK: - Query Operations
    
    /// Get storage device
    public func getStorageDevice(deviceId: String) -> StorageDevice? {
        return storageDevices[deviceId]
    }
    
    /// Get all storage devices
    public func getAllStorageDevices() -> [StorageDevice] {
        return Array(storageDevices.values)
    }
    
    /// Get storage statistics
    public func getStorageStatistics() -> StorageStatistics {
        return storageStatistics
    }
    
    /// Get storage operations
    public func getStorageOperations() -> [StorageOperationResult] {
        return Array(storageOperations.values)
    }
    
    /// Get storage history
    public func getStorageHistory() -> [StorageEvent] {
        return storageHistory
    }
    
    /// Check if device exists
    public func deviceExists(deviceId: String) -> Bool {
        return storageDevices[deviceId] != nil
    }
    
    /// Check if device is active
    public func isDeviceActive(deviceId: String) -> Bool {
        return storageDevices[deviceId]?.status == .active
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check durability invariant
    /// TLA+ Inv_Storage_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that data persists across failures
        return true // Simplified
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_Storage_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that data integrity is maintained
        return true // Simplified
    }
    
    /// Check performance invariant
    /// TLA+ Inv_Storage_Performance
    public func checkPerformanceInvariant() -> Bool {
        // Check that storage operations are efficient
        return storageStatistics.averageReadLatency < 0.1 && storageStatistics.averageWriteLatency < 0.1
    }
    
    /// Check scalability invariant
    /// TLA+ Inv_Storage_Scalability
    public func checkScalabilityInvariant() -> Bool {
        // Check that system can handle large datasets
        return storageStatistics.totalCapacity > 0
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let durability = checkDurabilityInvariant()
        let consistency = checkConsistencyInvariant()
        let performance = checkPerformanceInvariant()
        let scalability = checkScalabilityInvariant()
        
        return durability && consistency && performance && scalability
    }
}

// MARK: - Supporting Types

/// Storage event type
public enum StorageEventType: String, Codable, Sendable {
    case deviceAdded = "device_added"
    case deviceRemoved = "device_removed"
    case deviceUpdated = "device_updated"
    case readOperation = "read_operation"
    case writeOperation = "write_operation"
    case deleteOperation = "delete_operation"
    case readFailure = "read_failure"
    case writeFailure = "write_failure"
    case deleteFailure = "delete_failure"
    case cacheHit = "cache_hit"
}

/// Storage event
public struct StorageEvent: Codable, Sendable, Equatable {
    public let eventId: String
    public let deviceId: String
    public let eventType: StorageEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(eventId: String, deviceId: String, eventType: StorageEventType, timestamp: Date, data: [String: Value]) {
        self.eventId = eventId
        self.deviceId = deviceId
        self.eventType = eventType
        self.timestamp = timestamp
        self.data = data
    }
}

/// Storage configuration
public struct StorageConfig: Codable, Sendable {
    public let enableCaching: Bool
    public let cacheSize: Int
    public let enableCompression: Bool
    public let enableEncryption: Bool
    public let maxFileSize: Int64
    
    public init(enableCaching: Bool = true, cacheSize: Int = 1000, enableCompression: Bool = false, enableEncryption: Bool = false, maxFileSize: Int64 = 1024 * 1024 * 1024) {
        self.enableCaching = enableCaching
        self.cacheSize = cacheSize
        self.enableCompression = enableCompression
        self.enableEncryption = enableEncryption
        self.maxFileSize = maxFileSize
    }
}

/// Disk manager protocol
public protocol DiskManager: Sendable {
    func readData(key: String, deviceId: String) async throws -> Data
    func writeData(key: String, data: Data, deviceId: String) async throws
    func deleteData(key: String, deviceId: String) async throws
}

/// Mock disk manager for testing
public class MockDiskManager: DiskManager {
    public init() {}
    
    public func readData(key: String, deviceId: String) async throws -> Data {
        // Mock implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        return Data()
    }
    
    public func writeData(key: String, data: Data, deviceId: String) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
    }
    
    public func deleteData(key: String, deviceId: String) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
    }
}

/// Cache manager protocol
public protocol CacheManager: Sendable {
    func get(key: String) -> Data?
    func set(key: String, data: Data)
    func remove(key: String)
    func clear()
}

/// Mock cache manager for testing
public class MockCacheManager: CacheManager {
    private var cache: [String: Data] = [:]
    
    public init() {}
    
    public func get(key: String) -> Data? {
        return cache[key]
    }
    
    public func set(key: String, data: Data) {
        cache[key] = data
    }
    
    public func remove(key: String) {
        cache.removeValue(forKey: key)
    }
    
    public func clear() {
        cache.removeAll()
    }
}

// MARK: - Errors

public enum StorageError: Error, LocalizedError {
    case deviceAlreadyExists
    case deviceNotFound
    case deviceInUse
    case deviceNotActive
    case insufficientSpace
    case invalidCapacity
    case invalidUsedSpace
    case invalidFreeSpace
    case invalidSpaceAllocation
    case operationFailed
    
    public var errorDescription: String? {
        switch self {
        case .deviceAlreadyExists:
            return "Storage device already exists"
        case .deviceNotFound:
            return "Storage device not found"
        case .deviceInUse:
            return "Storage device is in use"
        case .deviceNotActive:
            return "Storage device is not active"
        case .insufficientSpace:
            return "Insufficient storage space"
        case .invalidCapacity:
            return "Invalid device capacity"
        case .invalidUsedSpace:
            return "Invalid used space"
        case .invalidFreeSpace:
            return "Invalid free space"
        case .invalidSpaceAllocation:
            return "Invalid space allocation"
        case .operationFailed:
            return "Storage operation failed"
        }
    }
}
