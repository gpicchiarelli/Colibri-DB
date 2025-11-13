//
//  MigrateCommand.swift
//  ColibrìDB Format Migration CLI
//
//  Usage:
//    coldb migrate --from 0.9.0 --to 1.0.0 --file database.colibri --verify
//

import Foundation
import ColibriCore

/// CLI command for format migration
public struct MigrateCommand {
    
    public static func run(arguments: [String]) async throws {
        let parser = ArgumentParser(arguments: arguments)
        
        guard let fromVersionStr = parser.value(for: "--from"),
              let toVersionStr = parser.value(for: "--to"),
              let filePath = parser.value(for: "--file") else {
            printUsage()
            return
        }
        
        let verify = parser.hasFlag("--verify")
        
        // Parse versions
        let fromVersion = try parseVersion(fromVersionStr)
        let toVersion = try parseVersion(toVersionStr)
        
        print("📦 ColibrìDB Format Migration Tool")
        print("================================")
        print("File:     \(filePath)")
        print("From:     \(fromVersion.description)")
        print("To:       \(toVersion.description)")
        print("Verify:   \(verify)")
        print("")
        
        // Read file
        let fileURL = URL(fileURLWithPath: filePath)
        guard FileManager.default.fileExists(atPath: fileURL.path) else {
            throw MigrationToolError.fileNotFound(filePath)
        }
        
        let originalData = try Data(contentsOf: fileURL)
        print("✓ Loaded file (\(originalData.count) bytes)")
        
        // Migrate
        let migrator = OnDiskFormatMigrator()
        let direction: MigrationDirection = toVersion > fromVersion ? .upgrade : .downgrade
        
        print("🔄 Migrating...")
        let migratedData = try await migrator.migrate(
            data: originalData,
            from: fromVersion,
            to: toVersion,
            direction: direction
        )
        print("✓ Migration complete (\(migratedData.count) bytes)")
        
        // Verify if requested
        if verify {
            print("🔍 Verifying migration integrity...")
            let isValid = try await migrator.verifyMigration(
                original: originalData,
                migrated: migratedData,
                from: fromVersion,
                to: toVersion
            )
            
            if isValid {
                print("✓ Migration verified: data integrity preserved")
            } else {
                throw MigrationToolError.verificationFailed
            }
        }
        
        // Write migrated file
        let outputPath = filePath + ".migrated"
        try migratedData.write(to: URL(fileURLWithPath: outputPath))
        print("✓ Written to: \(outputPath)")
        
        print("\n✅ Migration successful!")
    }
    
    private static func parseVersion(_ str: String) throws -> FormatVersion {
        let components = str.split(separator: ".").compactMap { UInt16($0) }
        guard components.count == 3 else {
            throw MigrationToolError.invalidVersion(str)
        }
        return FormatVersion(major: components[0], minor: components[1], patch: components[2])
    }
    
    private static func printUsage() {
        print("""
        Usage: coldb migrate --from VERSION --to VERSION --file FILE [--verify]
        
        Options:
          --from VERSION    Source format version (e.g., 0.9.0)
          --to VERSION      Target format version (e.g., 1.0.0)
          --file FILE       Database file to migrate
          --verify          Verify migration integrity (optional)
        
        Example:
          coldb migrate --from 0.9.0 --to 1.0.0 --file mydb.colibri --verify
        """)
    }
}

/// Argument parser
struct ArgumentParser {
    private let arguments: [String]
    
    init(arguments: [String]) {
        self.arguments = arguments
    }
    
    func value(for flag: String) -> String? {
        guard let index = arguments.firstIndex(of: flag),
              index + 1 < arguments.count else {
            return nil
        }
        return arguments[index + 1]
    }
    
    func hasFlag(_ flag: String) -> Bool {
        return arguments.contains(flag)
    }
}

/// Migration tool errors
enum MigrationToolError: Error, LocalizedError {
    case fileNotFound(String)
    case invalidVersion(String)
    case verificationFailed
    
    var errorDescription: String? {
        switch self {
        case .fileNotFound(let path):
            return "File not found: \(path)"
        case .invalidVersion(let version):
            return "Invalid version format: \(version)"
        case .verificationFailed:
            return "Migration verification failed"
        }
    }
}

