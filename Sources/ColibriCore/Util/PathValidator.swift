//
//  PathValidator.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: 🛡️ Path validation and sanitization to prevent path traversal attacks

import Foundation

/// 🔧 FIX: Comprehensive path validation to prevent path traversal vulnerabilities
public struct PathValidator {
    
    // MARK: - Security Configuration
    
    /// Maximum allowed path length to prevent DoS
    public static let maxPathLength = 4096
    
    /// Allowed file extensions for database files
    public static let allowedExtensions: Set<String> = [
        "dat", "wal", "bt", "fsm", "json", "log", "tmp", "backup", "snapshot"
    ]
    
    /// Base directories that are considered safe
    private static nonisolated(unsafe) var _safeBases: Set<String> = []
    private static let safeBasesLock = NSLock()
    
    // MARK: - Public API
    
    /// Initialize the validator with safe base directories
    public static func configure(safeBases: [String]) {
        safeBasesLock.lock()
        defer { safeBasesLock.unlock() }
        _safeBases = Set(safeBases.map { canonicalizePath($0) })
        print("🛡️ PathValidator configured with \(safeBases.count) safe base directories")
    }
    
    /// Validate and sanitize a file path
    /// - Parameter path: The path to validate
    /// - Returns: Sanitized safe path
    /// - Throws: DBError if path is invalid or unsafe
    public static func validatePath(_ path: String) throws -> String {
        // Basic validation
        try validateBasicSafety(path)
        
        // Canonicalize and resolve the path
        let canonicalPath = canonicalizePath(path)
        
        // Check against safe bases
        try validateAgainstSafeBases(canonicalPath)
        
        // Additional security checks
        try validateSecurityConstraints(canonicalPath)
        
        print("✅ Path validated: \(canonicalPath)")
        return canonicalPath
    }
    
    /// Create a safe path within a base directory
    /// - Parameters:
    ///   - baseDir: Base directory (must be configured as safe)
    ///   - filename: Filename to append
    /// - Returns: Safe full path
    /// - Throws: DBError if path construction fails
    public static func createSafePath(baseDir: String, filename: String) throws -> String {
        let sanitizedBase = try validatePath(baseDir)
        let sanitizedFilename = try sanitizeFilename(filename)
        
        let fullPath = URL(fileURLWithPath: sanitizedBase)
            .appendingPathComponent(sanitizedFilename)
            .path
        
        return try validatePath(fullPath)
    }
    
    // MARK: - Validation Methods
    
    public static func validateBasicSafety(_ path: String) throws {
        // Check for null bytes
        if path.contains("\0") {
            throw DBError.invalidArgument("Path contains null bytes")
        }
        
        // Check length
        if path.count > maxPathLength {
            throw DBError.invalidArgument("Path too long (max: \(maxPathLength))")
        }
        
        // Check for empty path
        if path.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty {
            throw DBError.invalidArgument("Empty path not allowed")
        }
        
        // Check for dangerous patterns
        let dangerousPatterns = [
            "../",           // Path traversal
            "..\\",          // Windows path traversal
            "/..",           // Path traversal at end
            "\\..",          // Windows path traversal at end
            "//",            // Double slashes
            "\\\\",          // Double backslashes
            "~",             // Home directory expansion
            "$",             // Environment variable expansion
            "`",             // Command substitution
            "|",             // Pipe
            ";",             // Command separator
            "&",             // Background process
            "$()",           // Command substitution
            "${}"            // Variable expansion
        ]
        
        for pattern in dangerousPatterns {
            if path.contains(pattern) {
                throw DBError.invalidArgument("Path contains dangerous pattern: \(pattern)")
            }
        }
    }
    
    private static func validateAgainstSafeBases(_ canonicalPath: String) throws {
        safeBasesLock.lock()
        let currentSafeBases = _safeBases
        safeBasesLock.unlock()
        
        guard !currentSafeBases.isEmpty else {
            throw DBError.invalidArgument("No safe base directories configured")
        }
        
        let isWithinSafeBase = currentSafeBases.contains { safeBase in
            canonicalPath.hasPrefix(safeBase + "/") || canonicalPath == safeBase
        }
        
        if !isWithinSafeBase {
            throw DBError.invalidArgument("Path outside safe directories: \(canonicalPath)")
        }
    }
    
    private static func validateSecurityConstraints(_ path: String) throws {
        let url = URL(fileURLWithPath: path)
        
        // Check file extension if it has one
        if !url.pathExtension.isEmpty {
            let ext = url.pathExtension.lowercased()
            if !allowedExtensions.contains(ext) {
                throw DBError.invalidArgument("File extension not allowed: .\(ext)")
            }
        }
        
        // Check for hidden files (starting with .)
        let filename = url.lastPathComponent
        if filename.hasPrefix(".") && filename != "." && filename != ".." {
            throw DBError.invalidArgument("Hidden files not allowed: \(filename)")
        }
        
        // Check for system directories
        let systemDirs = ["/etc", "/usr", "/bin", "/sbin", "/System", "/Library", "/Applications"]
        for sysDir in systemDirs {
            if path.hasPrefix(sysDir) {
                throw DBError.invalidArgument("Access to system directory not allowed: \(sysDir)")
            }
        }
    }
    
    private static func sanitizeFilename(_ filename: String) throws -> String {
        // Remove dangerous characters
        let dangerous = CharacterSet(charactersIn: "<>:\"|?*\\/\0")
        let sanitized = filename.components(separatedBy: dangerous).joined()
        
        // Check length
        if sanitized.count > 255 {
            throw DBError.invalidArgument("Filename too long (max: 255)")
        }
        
        // Check for reserved names (Windows compatibility)
        let reserved = ["CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", 
                       "COM5", "COM6", "COM7", "COM8", "COM9", "LPT1", "LPT2", 
                       "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9"]
        
        if reserved.contains(sanitized.uppercased()) {
            throw DBError.invalidArgument("Reserved filename: \(sanitized)")
        }
        
        return sanitized
    }
    
    public static func canonicalizePath(_ path: String) -> String {
        let url = URL(fileURLWithPath: path)
        return url.standardized.path
    }
    
    // MARK: - Convenience Methods
    
    /// Validate a data directory path
    public static func validateDataDir(_ path: String) throws -> String {
        let validated = try validatePath(path)
        
        // Ensure directory exists or can be created
        let fm = FileManager.default
        var isDir: ObjCBool = false
        
        if fm.fileExists(atPath: validated, isDirectory: &isDir) {
            if !isDir.boolValue {
                throw DBError.invalidArgument("Data directory path is not a directory: \(validated)")
            }
        } else {
            // Try to create directory
            do {
                try fm.createDirectory(atPath: validated, withIntermediateDirectories: true)
                print("📁 Created data directory: \(validated)")
            } catch {
                throw DBError.io("Cannot create data directory: \(error)")
            }
        }
        
        return validated
    }
    
    /// Validate a file path for reading
    public static func validateFileForReading(_ path: String) throws -> String {
        let validated = try validatePath(path)
        
        let fm = FileManager.default
        if !fm.fileExists(atPath: validated) {
            throw DBError.notFound("File not found: \(validated)")
        }
        
        if !fm.isReadableFile(atPath: validated) {
            throw DBError.invalidArgument("File not readable: \(validated)")
        }
        
        return validated
    }
    
    /// Validate a file path for writing
    public static func validateFileForWriting(_ path: String) throws -> String {
        let validated = try validatePath(path)
        
        let fm = FileManager.default
        let dir = URL(fileURLWithPath: validated).deletingLastPathComponent().path
        
        // Ensure parent directory exists
        if !fm.fileExists(atPath: dir) {
            do {
                try fm.createDirectory(atPath: dir, withIntermediateDirectories: true)
                print("📁 Created directory: \(dir)")
            } catch {
                throw DBError.io("Cannot create directory: \(error)")
            }
        }
        
        // Check if file exists and is writable
        if fm.fileExists(atPath: validated) && !fm.isWritableFile(atPath: validated) {
            throw DBError.invalidArgument("File not writable: \(validated)")
        }
        
        return validated
    }
}

// MARK: - Extensions

extension DBConfig {
    /// 🔧 FIX: Validate all paths in configuration
    public func validatePaths() throws {
        // First, do basic validation without safe base checking
        try PathValidator.validateBasicSafety(self.dataDir)
        
        // Canonicalize the path
        let canonicalDataDir = PathValidator.canonicalizePath(self.dataDir)
        
        // Configure safe bases with the canonical path
        PathValidator.configure(safeBases: [canonicalDataDir])
        
        // Now validate the data directory properly
        let _ = try PathValidator.validateDataDir(canonicalDataDir)
        
        print("✅ DBConfig paths validated successfully")
    }
}
