//
//  APFSOptimizations.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//

// Theme: APFS-specific optimizations for Apple Silicon.

import Foundation
import os.log
import Dispatch

#if os(macOS)
import Darwin
#endif

public struct APFSOptimizations {
    private static let logger = Logger(subsystem: "com.colibridb", category: "apfs-optimizations")
    
    /// Create APFS snapshot for backup
    public static func createSnapshot(at path: String, name: String) throws -> String {
        #if os(macOS)
        let snapshotName = "\(name)_\(Date().timeIntervalSince1970)"
        
        // Use tmutil to create snapshot
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tmutil")
        process.arguments = ["snapshot", path, "-n", snapshotName]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to create APFS snapshot: \(error)")
        }
        
        logger.info("Created APFS snapshot: \(snapshotName)")
        return snapshotName
        #else
        throw DBError.io("APFS snapshots not available on this platform")
        #endif
    }
    
    /// List available APFS snapshots
    public static func listSnapshots(for path: String) throws -> [String] {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tmutil")
        process.arguments = ["listlocalsnapshots", path]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to list APFS snapshots: \(error)")
        }
        
        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        let output = String(data: data, encoding: .utf8) ?? ""
        
        let snapshots = output.components(separatedBy: .newlines)
            .filter { !$0.isEmpty }
            .map { $0.trimmingCharacters(in: .whitespaces) }
        
        logger.info("Found \(snapshots.count) APFS snapshots")
        return snapshots
        #else
        return []
        #endif
    }
    
    /// Delete APFS snapshot
    public static func deleteSnapshot(_ snapshotName: String) throws {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tmutil")
        process.arguments = ["deletelocalsnapshots", snapshotName]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to delete APFS snapshot: \(error)")
        }
        
        logger.info("Deleted APFS snapshot: \(snapshotName)")
        #else
        throw DBError.io("APFS snapshots not available on this platform")
        #endif
    }
    
    /// Create APFS clone for fast table/index snapshots
    public static func createClone(sourcePath: String, destinationPath: String) throws {
        #if os(macOS)
        // Use cp with -c flag for APFS clone
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/bin/cp")
        process.arguments = ["-c", sourcePath, destinationPath]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to create APFS clone: \(error)")
        }
        
        logger.info("Created APFS clone: \(sourcePath) -> \(destinationPath)")
        #else
        // Fallback to regular copy
        try FileManager.default.copyItem(atPath: sourcePath, toPath: destinationPath)
        #endif
    }
    
    /// Check if file is on APFS filesystem
    public static func isAPFSVolume(_ path: String) -> Bool {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/sbin/diskutil")
        process.arguments = ["info", path]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        do {
            try process.run()
            process.waitUntilExit()
            
            if process.terminationStatus == 0 {
                let data = pipe.fileHandleForReading.readDataToEndOfFile()
                let output = String(data: data, encoding: .utf8) ?? ""
                return output.contains("File System Personality: APFS")
            }
        } catch {
            logger.error("Failed to check filesystem type: \(error)")
        }
        #endif
        return false
    }
    
    /// Get APFS volume information
    public static func getVolumeInfo(_ path: String) throws -> [String: String] {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/sbin/diskutil")
        process.arguments = ["info", path]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to get volume info: \(error)")
        }
        
        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        let output = String(data: data, encoding: .utf8) ?? ""
        
        var info: [String: String] = [:]
        let lines = output.components(separatedBy: .newlines)
        
        for line in lines {
            let components = line.components(separatedBy: ":")
            if components.count == 2 {
                let key = components[0].trimmingCharacters(in: .whitespaces)
                let value = components[1].trimmingCharacters(in: .whitespaces)
                info[key] = value
            }
        }
        
        logger.info("Retrieved volume info: \(info.count) properties")
        return info
        #else
        return [:]
        #endif
    }
    
    /// Enable APFS compression for database files
    public static func enableCompression(for path: String) throws {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/compression_tool")
        process.arguments = ["-encode", path]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to enable compression: \(error)")
        }
        
        logger.info("Enabled APFS compression for: \(path)")
        #else
        logger.info("APFS compression not available on this platform")
        #endif
    }
    
    /// Create incremental backup using APFS snapshots
    public static func createIncrementalBackup(sourcePath: String, destinationPath: String, baseSnapshot: String? = nil) throws -> String {
        #if os(macOS)
        let snapshotName = try createSnapshot(at: sourcePath, name: "backup_\(Date().timeIntervalSince1970)")
        
        if let baseSnapshot = baseSnapshot {
            // Create incremental backup from base snapshot
            let process = Process()
            process.executableURL = URL(fileURLWithPath: "/usr/bin/rsync")
            process.arguments = [
                "-a", "--delete", "--hard-links", "--acls", "--xattrs",
                "--link-dest=\(baseSnapshot)",
                "\(sourcePath)/",
                destinationPath
            ]
            
            let pipe = Pipe()
            process.standardOutput = pipe
            process.standardError = pipe
            
            try process.run()
            process.waitUntilExit()
            
            if process.terminationStatus != 0 {
                let data = pipe.fileHandleForReading.readDataToEndOfFile()
                let error = String(data: data, encoding: .utf8) ?? "Unknown error"
                throw DBError.io("Failed to create incremental backup: \(error)")
            }
        } else {
            // Create full backup
            try createClone(sourcePath: sourcePath, destinationPath: destinationPath)
        }
        
        logger.info("Created incremental backup: \(snapshotName)")
        return snapshotName
        #else
        // Fallback to regular backup
        try FileManager.default.copyItem(atPath: sourcePath, toPath: destinationPath)
        return "backup_\(Date().timeIntervalSince1970)"
        #endif
    }
    
    /// Restore from APFS snapshot
    public static func restoreFromSnapshot(_ snapshotName: String, to path: String) throws {
        #if os(macOS)
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tmutil")
        process.arguments = ["restore", snapshotName, path]
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        try process.run()
        process.waitUntilExit()
        
        if process.terminationStatus != 0 {
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let error = String(data: data, encoding: .utf8) ?? "Unknown error"
            throw DBError.io("Failed to restore from snapshot: \(error)")
        }
        
        logger.info("Restored from APFS snapshot: \(snapshotName)")
        #else
        throw DBError.io("APFS snapshots not available on this platform")
        #endif
    }
}
