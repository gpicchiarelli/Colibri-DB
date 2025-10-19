//
//  BackupManager.swift
//  Based on: spec/Backup.tla
//

import Foundation

public enum BackupType {
    case full
    case incremental
    case differential
}

public struct BackupMetadata: Codable {
    public let id: UUID
    public let type: BackupType
    public let startTime: Date
    public let endTime: Date?
    public let baseBackupId: UUID?
    public let lsn: LSN
    public let size: Int64
    
    enum CodingKeys: String, CodingKey {
        case id, startTime, endTime, baseBackupId, lsn, size
        case type
    }
    
    public init(id: UUID, type: BackupType, startTime: Date, endTime: Date?, baseBackupId: UUID?, lsn: LSN, size: Int64) {
        self.id = id
        self.type = type
        self.startTime = startTime
        self.endTime = endTime
        self.baseBackupId = baseBackupId
        self.lsn = lsn
        self.size = size
    }
    
    public func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(id, forKey: .id)
        try container.encode(startTime, forKey: .startTime)
        try container.encode(endTime, forKey: .endTime)
        try container.encode(baseBackupId, forKey: .baseBackupId)
        try container.encode(lsn, forKey: .lsn)
        try container.encode(size, forKey: .size)
        
        let typeString: String
        switch type {
        case .full: typeString = "full"
        case .incremental: typeString = "incremental"
        case .differential: typeString = "differential"
        }
        try container.encode(typeString, forKey: .type)
    }
    
    public init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        id = try container.decode(UUID.self, forKey: .id)
        startTime = try container.decode(Date.self, forKey: .startTime)
        endTime = try container.decodeIfPresent(Date.self, forKey: .endTime)
        baseBackupId = try container.decodeIfPresent(UUID.self, forKey: .baseBackupId)
        lsn = try container.decode(LSN.self, forKey: .lsn)
        size = try container.decode(Int64.self, forKey: .size)
        
        let typeString = try container.decode(String.self, forKey: .type)
        switch typeString {
        case "full": type = .full
        case "incremental": type = .incremental
        case "differential": type = .differential
        default: type = .full
        }
    }
}

public actor BackupManager {
    private let backupDirectory: URL
    private let wal: FileWAL
    private let bufferPool: BufferPool
    private var backupHistory: [BackupMetadata] = []
    
    public init(backupDirectory: URL, wal: FileWAL, bufferPool: BufferPool) {
        self.backupDirectory = backupDirectory
        self.wal = wal
        self.bufferPool = bufferPool
    }
    
    public func createBackup(type: BackupType) async throws -> BackupMetadata {
        let backupId = UUID()
        let startTime = Date()
        let currentLSN = await wal.getCurrentLSN()
        
        try await bufferPool.flushAll()
        try await wal.flush()
        
        let backupPath = backupDirectory.appendingPathComponent(backupId.uuidString)
        try FileManager.default.createDirectory(at: backupPath, withIntermediateDirectories: true)
        
        let size: Int64 = 0
        
        let metadata = BackupMetadata(
            id: backupId,
            type: type,
            startTime: startTime,
            endTime: Date(),
            baseBackupId: nil,
            lsn: currentLSN,
            size: size
        )
        
        backupHistory.append(metadata)
        
        let encoder = JSONEncoder()
        let metadataData = try encoder.encode(metadata)
        try metadataData.write(to: backupPath.appendingPathComponent("metadata.json"))
        
        return metadata
    }
    
    public func restoreBackup(backupId: UUID) async throws {
        guard let metadata = backupHistory.first(where: { $0.id == backupId }) else {
            throw DBError.notFound
        }
        
        let backupPath = backupDirectory.appendingPathComponent(backupId.uuidString)
        
        print("Restoring backup \(backupId) from \(metadata.startTime)")
    }
    
    public func listBackups() -> [BackupMetadata] {
        return backupHistory
    }
    
    public func deleteBackup(backupId: UUID) throws {
        guard let index = backupHistory.firstIndex(where: { $0.id == backupId }) else {
            throw DBError.notFound
        }
        
        backupHistory.remove(at: index)
        
        let backupPath = backupDirectory.appendingPathComponent(backupId.uuidString)
        try FileManager.default.removeItem(at: backupPath)
    }
}

