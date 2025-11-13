//
//  OnDiskFormat.swift
//  ColibrìDB On-Disk Format Version Management
//
//  Exit Criteria: FORMAT_VERSION, tool migrate up/down, canary
//  upgrade/downgrade su 3 versioni consecutive => dati invariati
//

import Foundation

/// On-disk format version
public struct FormatVersion: Codable, Comparable, Sendable {
    public let major: UInt16
    public let minor: UInt16
    public let patch: UInt16
    
    public init(major: UInt16, minor: UInt16, patch: UInt16) {
        self.major = major
        self.minor = minor
        self.patch = patch
    }
    
    public static func < (lhs: FormatVersion, rhs: FormatVersion) -> Bool {
        if lhs.major != rhs.major { return lhs.major < rhs.major }
        if lhs.minor != rhs.minor { return lhs.minor < rhs.minor }
        return lhs.patch < rhs.patch
    }
    
    public var description: String {
        return "\(major).\(minor).\(patch)"
    }
    
    // Current production format version
    public static let current = FormatVersion(major: 1, minor: 0, patch: 0)
    
    // Supported versions (for backward compatibility)
    public static let supported: [FormatVersion] = [
        FormatVersion(major: 1, minor: 0, patch: 0),  // v1.0.0 - current
        FormatVersion(major: 0, minor: 9, patch: 0),  // v0.9.0 - beta
        FormatVersion(major: 0, minor: 8, patch: 0),  // v0.8.0 - alpha
    ]
    
    public func isCompatible(with other: FormatVersion) -> Bool {
        // Same major version is compatible
        return self.major == other.major
    }
}

/// On-disk file header with version
public struct OnDiskFileHeader: Codable, Sendable {
    public static let magic: UInt64 = 0x434F4C4942524944  // 'COLIBRID'
    public static let headerSize: Int = 64
    
    public let magic: UInt64
    public let formatVersion: FormatVersion
    public let createdAt: Date
    public let checksum: UInt32
    public let flags: UInt32
    public let reserved: Data  // 36 bytes reserved for future use
    
    public init(formatVersion: FormatVersion = .current, flags: UInt32 = 0) {
        self.magic = Self.magic
        self.formatVersion = formatVersion
        self.createdAt = Date()
        self.checksum = 0  // Will be calculated
        self.flags = flags
        self.reserved = Data(count: 36)
    }
    
    public var isValid: Bool {
        return magic == Self.magic && 
               FormatVersion.supported.contains(formatVersion)
    }
    
    public func serialize() throws -> Data {
        let encoder = JSONEncoder()
        return try encoder.encode(self)
    }
    
    public static func deserialize(from data: Data) throws -> OnDiskFileHeader {
        let decoder = JSONDecoder()
        return try decoder.decode(OnDiskFileHeader.self, from: data)
    }
}

/// Migration direction
public enum MigrationDirection {
    case upgrade
    case downgrade
}

/// Migration step protocol
public protocol MigrationStep: Sendable {
    var fromVersion: FormatVersion { get }
    var toVersion: FormatVersion { get }
    
    func apply(to data: Data) async throws -> Data
    func rollback(from data: Data) async throws -> Data
}

/// Migration manager
public actor OnDiskFormatMigrator {
    
    private var migrations: [MigrationStep] = []
    
    public init() {
        // Register migrations
        self.migrations = []
        self.migrations.append(Migration_v0_8_to_v0_9())
        self.migrations.append(Migration_v0_9_to_v1_0())
    }
    
    private func registerDefaultMigrations() async {
        // Migration from v0.8.0 to v0.9.0
        migrations.append(Migration_v0_8_to_v0_9())
        
        // Migration from v0.9.0 to v1.0.0
        migrations.append(Migration_v0_9_to_v1_0())
    }
    
    /// Migrate data from one version to another
    public func migrate(
        data: Data,
        from: FormatVersion,
        to: FormatVersion,
        direction: MigrationDirection
    ) async throws -> Data {
        
        guard from != to else { return data }
        
        // Find migration path
        let path = try findMigrationPath(from: from, to: to)
        
        var currentData = data
        
        switch direction {
        case .upgrade:
            for step in path {
                currentData = try await step.apply(to: currentData)
            }
        case .downgrade:
            for step in path.reversed() {
                currentData = try await step.rollback(from: currentData)
            }
        }
        
        return currentData
    }
    
    /// Find migration path between versions
    private func findMigrationPath(
        from: FormatVersion,
        to: FormatVersion
    ) throws -> [MigrationStep] {
        
        var path: [MigrationStep] = []
        var current = from
        
        while current < to {
            // Find next migration step
            guard let step = migrations.first(where: { $0.fromVersion == current && $0.toVersion <= to }) else {
                throw FormatMigrationError.noMigrationPath(from: from, to: to)
            }
            
            path.append(step)
            current = step.toVersion
        }
        
        if current != to {
            throw FormatMigrationError.noMigrationPath(from: from, to: to)
        }
        
        return path
    }
    
    /// Verify migration integrity
    public func verifyMigration(
        original: Data,
        migrated: Data,
        from: FormatVersion,
        to: FormatVersion
    ) async throws -> Bool {
        
        // Canary test: migrate back and compare
        let rolledBack = try await migrate(
            data: migrated,
            from: to,
            to: from,
            direction: .downgrade
        )
        
        // Compare original and rolled-back data
        return original == rolledBack
    }
}

// MARK: - Migration Implementations

/// Migration from v0.8.0 to v0.9.0
struct Migration_v0_8_to_v0_9: MigrationStep {
    let fromVersion = FormatVersion(major: 0, minor: 8, patch: 0)
    let toVersion = FormatVersion(major: 0, minor: 9, patch: 0)
    
    func apply(to data: Data) async throws -> Data {
        // Add new fields for v0.9.0
        // Example: Add index metadata
        var migratedData = data
        let indexMetadata = Data([0x00, 0x01])  // Dummy metadata
        migratedData.append(indexMetadata)
        return migratedData
    }
    
    func rollback(from data: Data) async throws -> Data {
        // Remove fields added in v0.9.0
        guard data.count >= 2 else {
            throw FormatMigrationError.invalidFormat
        }
        return data.dropLast(2)
    }
}

/// Migration from v0.9.0 to v1.0.0
struct Migration_v0_9_to_v1_0: MigrationStep {
    let fromVersion = FormatVersion(major: 0, minor: 9, patch: 0)
    let toVersion = FormatVersion(major: 1, minor: 0, patch: 0)
    
    func apply(to data: Data) async throws -> Data {
        // Finalize format for v1.0.0
        // Example: Add checksum
        var migratedData = data
        let checksum = CRC32Accelerator.calculate(data)
        withUnsafeBytes(of: checksum.bigEndian) {
            migratedData.append(contentsOf: $0)
        }
        return migratedData
    }
    
    func rollback(from data: Data) async throws -> Data {
        // Remove checksum
        guard data.count >= 4 else {
            throw FormatMigrationError.invalidFormat
        }
        return data.dropLast(4)
    }
}

// MARK: - Errors

public enum FormatMigrationError: Error, LocalizedError {
    case unsupportedVersion(FormatVersion)
    case noMigrationPath(from: FormatVersion, to: FormatVersion)
    case invalidFormat
    case checksumMismatch
    case migrationFailed(String)
    
    public var errorDescription: String? {
        switch self {
        case .unsupportedVersion(let version):
            return "Unsupported format version: \(version.description)"
        case .noMigrationPath(let from, let to):
            return "No migration path from \(from.description) to \(to.description)"
        case .invalidFormat:
            return "Invalid on-disk format"
        case .checksumMismatch:
            return "Checksum mismatch after migration"
        case .migrationFailed(let reason):
            return "Migration failed: \(reason)"
        }
    }
}

