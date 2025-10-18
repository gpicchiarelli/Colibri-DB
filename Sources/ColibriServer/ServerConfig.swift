//
//  ServerConfig.swift
//  coldb-server
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Server configuration and management

import Foundation
import NIO

// MARK: - Server Configuration

public struct ServerConfiguration {
    public let host: String
    public let port: Int
    public let dataDirectory: String
    public let maxConnections: Int
    public let sslEnabled: Bool
    public let sslCertificatePath: String?
    public let sslPrivateKeyPath: String?
    public let logLevel: LogLevel
    public let connectionTimeout: TimeInterval
    public let queryTimeout: TimeInterval
    
    public init(
        host: String = "0.0.0.0",
        port: Int = 5432,
        dataDirectory: String = "./data",
        maxConnections: Int = 1000,
        sslEnabled: Bool = false,
        sslCertificatePath: String? = nil,
        sslPrivateKeyPath: String? = nil,
        logLevel: LogLevel = .info,
        connectionTimeout: TimeInterval = 30.0,
        queryTimeout: TimeInterval = 60.0
    ) {
        self.host = host
        self.port = port
        self.dataDirectory = dataDirectory
        self.maxConnections = maxConnections
        self.sslEnabled = sslEnabled
        self.sslCertificatePath = sslCertificatePath
        self.sslPrivateKeyPath = sslPrivateKeyPath
        self.logLevel = logLevel
        self.connectionTimeout = connectionTimeout
        self.queryTimeout = queryTimeout
    }
}

// MARK: - Log Level

public enum LogLevel: String, CaseIterable {
    case debug = "DEBUG"
    case info = "INFO"
    case warning = "WARNING"
    case error = "ERROR"
    
    public var priority: Int {
        switch self {
        case .debug: return 0
        case .info: return 1
        case .warning: return 2
        case .error: return 3
        }
    }
}

// MARK: - Configuration Parser

public struct ConfigurationParser {
    public static func parse(from arguments: [String]) -> ServerConfiguration {
        var config = ServerConfiguration()
        
        var i = 0
        while i < arguments.count {
            let arg = arguments[i]
            
            switch arg {
            case "--host":
                if i + 1 < arguments.count {
                    let host = arguments[i + 1]
                    config = ServerConfiguration(
                        host: host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--port":
                if i + 1 < arguments.count, let port = Int(arguments[i + 1]) {
                    config = ServerConfiguration(
                        host: config.host,
                        port: port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--data-dir":
                if i + 1 < arguments.count {
                    let dir = arguments[i + 1]
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: dir,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--max-connections":
                if i + 1 < arguments.count, let maxConn = Int(arguments[i + 1]) {
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: maxConn,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--ssl":
                config = ServerConfiguration(
                    host: config.host,
                    port: config.port,
                    dataDirectory: config.dataDirectory,
                    maxConnections: config.maxConnections,
                    sslEnabled: true,
                    sslCertificatePath: config.sslCertificatePath,
                    sslPrivateKeyPath: config.sslPrivateKeyPath,
                    logLevel: config.logLevel,
                    connectionTimeout: config.connectionTimeout,
                    queryTimeout: config.queryTimeout
                )
            case "--ssl-cert":
                if i + 1 < arguments.count {
                    let cert = arguments[i + 1]
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: cert,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--ssl-key":
                if i + 1 < arguments.count {
                    let key = arguments[i + 1]
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: key,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--log-level":
                if i + 1 < arguments.count,
                   let level = LogLevel(rawValue: arguments[i + 1].uppercased()) {
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: level,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--connection-timeout":
                if i + 1 < arguments.count, let timeout = TimeInterval(arguments[i + 1]) {
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: timeout,
                        queryTimeout: config.queryTimeout
                    )
                    i += 1
                }
            case "--query-timeout":
                if i + 1 < arguments.count, let timeout = TimeInterval(arguments[i + 1]) {
                    config = ServerConfiguration(
                        host: config.host,
                        port: config.port,
                        dataDirectory: config.dataDirectory,
                        maxConnections: config.maxConnections,
                        sslEnabled: config.sslEnabled,
                        sslCertificatePath: config.sslCertificatePath,
                        sslPrivateKeyPath: config.sslPrivateKeyPath,
                        logLevel: config.logLevel,
                        connectionTimeout: config.connectionTimeout,
                        queryTimeout: timeout
                    )
                    i += 1
                }
            case "--config":
                if i + 1 < arguments.count {
                    config = loadFromFile(path: arguments[i + 1])
                    i += 1
                }
            case "--help":
                printHelp()
                exit(0)
            default:
                break
            }
            i += 1
        }
        
        return config
    }
    
    private static func loadFromFile(path: String) -> ServerConfiguration {
        // TODO: Implement configuration file loading
        return ServerConfiguration()
    }
    
    private static func printHelp() {
        print("ColibrDB Server")
        print("Usage: coldb-server [options]")
        print("")
        print("Options:")
        print("  --host HOST              Server host (default: 0.0.0.0)")
        print("  --port PORT              Server port (default: 5432)")
        print("  --data-dir DIR           Database directory (default: ./data)")
        print("  --max-connections NUM    Maximum connections (default: 1000)")
        print("  --ssl                    Enable SSL/TLS")
        print("  --ssl-cert PATH          SSL certificate file path")
        print("  --ssl-key PATH           SSL private key file path")
        print("  --log-level LEVEL        Log level: debug, info, warning, error (default: info)")
        print("  --connection-timeout SEC Connection timeout in seconds (default: 30)")
        print("  --query-timeout SEC      Query timeout in seconds (default: 60)")
        print("  --config PATH            Load configuration from file")
        print("  --help                   Show this help")
        print("")
        print("Examples:")
        print("  coldb-server --port 8080 --data-dir /var/lib/colibridb")
        print("  coldb-server --ssl --ssl-cert cert.pem --ssl-key key.pem")
        print("  coldb-server --config /etc/colibridb/server.conf")
    }
}

// MARK: - Configuration Validation

public struct ConfigurationValidator {
    public static func validate(_ config: ServerConfiguration) throws {
        // Validate host format
        try validateHost(config.host)
        
        // Validate port range
        guard config.port > 0 && config.port <= 65535 else {
            throw ConfigurationError.invalidPort(config.port)
        }
        
        // Warn about privileged ports
        if config.port < 1024 && config.port != 0 {
            print("⚠️  Warning: Port \(config.port) is a privileged port. May require root access.")
        }
        
        // Validate max connections
        guard config.maxConnections > 0 && config.maxConnections <= 100000 else {
            throw ConfigurationError.invalidMaxConnections(config.maxConnections)
        }
        
        // Validate data directory with security checks
        try validateDataDirectory(config.dataDirectory)
        
        // Validate SSL configuration
        if config.sslEnabled {
            guard let certPath = config.sslCertificatePath,
                  let keyPath = config.sslPrivateKeyPath else {
                throw ConfigurationError.sslConfigurationIncomplete
            }
            
            // Validate SSL certificate path
            try validateSSLFile(certPath, type: "certificate")
            
            // Validate SSL private key path
            try validateSSLFile(keyPath, type: "private key")
            
            // Warn about file permissions
            checkSSLFilePermissions(certPath, keyPath)
        }
        
        // Validate timeouts with reasonable bounds
        guard config.connectionTimeout > 0 && config.connectionTimeout <= 3600 else {
            throw ConfigurationError.invalidConnectionTimeout(config.connectionTimeout)
        }
        
        guard config.queryTimeout > 0 && config.queryTimeout <= 3600 else {
            throw ConfigurationError.invalidQueryTimeout(config.queryTimeout)
        }
        
        // Warn if timeouts are very long
        if config.connectionTimeout > 300 {
            print("⚠️  Warning: Connection timeout is very long (\(config.connectionTimeout)s)")
        }
        if config.queryTimeout > 300 {
            print("⚠️  Warning: Query timeout is very long (\(config.queryTimeout)s)")
        }
    }
    
    // MARK: - Private Validation Methods
    
    private static func validateHost(_ host: String) throws {
        guard !host.isEmpty else {
            throw ConfigurationError.invalidHost("Host cannot be empty")
        }
        
        // Check for valid format (IPv4, IPv6, hostname, or wildcard)
        if host == "0.0.0.0" || host == "::" || host == "*" {
            // Valid wildcard bindings
            return
        }
        
        // Validate IPv4
        if isValidIPv4(host) {
            return
        }
        
        // Validate IPv6 (with or without brackets)
        if isValidIPv6(host) {
            return
        }
        
        // Validate hostname/domain
        if isValidHostname(host) {
            return
        }
        
        throw ConfigurationError.invalidHost("Invalid host format: '\(host)'")
    }
    
    private static func isValidIPv4(_ string: String) -> Bool {
        let parts = string.split(separator: ".")
        guard parts.count == 4 else { return false }
        
        return parts.allSatisfy { part in
            guard let num = Int(part), num >= 0, num <= 255 else {
                return false
            }
            return true
        }
    }
    
    private static func isValidIPv6(_ string: String) -> Bool {
        let cleaned = string.trimmingCharacters(in: CharacterSet(charactersIn: "[]"))
        let parts = cleaned.split(separator: ":", omittingEmptySubsequences: false)
        
        // IPv6 has 8 groups (or less with :: compression)
        guard parts.count <= 8 else { return false }
        
        return parts.allSatisfy { part in
            if part.isEmpty { return true } // Allow :: compression
            guard part.count <= 4 else { return false }
            return part.allSatisfy { $0.isHexDigit }
        }
    }
    
    private static func isValidHostname(_ string: String) -> Bool {
        // Hostname can be alphanumeric, hyphens, and dots
        // Must not start/end with hyphen or dot
        let pattern = "^[a-zA-Z0-9]([a-zA-Z0-9\\-]{0,61}[a-zA-Z0-9])?(\\.[a-zA-Z0-9]([a-zA-Z0-9\\-]{0,61}[a-zA-Z0-9])?)*$"
        let regex = try? NSRegularExpression(pattern: pattern)
        let range = NSRange(string.startIndex..., in: string)
        return regex?.firstMatch(in: string, range: range) != nil
    }
    
    private static func validateDataDirectory(_ path: String) throws {
        // Check for path traversal attempts
        let normalized = (path as NSString).standardizingPath
        if normalized.contains("..") {
            throw ConfigurationError.invalidDataDirectory("Path contains '..' which is not allowed")
        }
        
        // Create directory if it doesn't exist
        let dataDir = URL(fileURLWithPath: normalized)
        if !FileManager.default.fileExists(atPath: normalized) {
            do {
                try FileManager.default.createDirectory(at: dataDir, withIntermediateDirectories: true)
                print("✅ Created data directory: \(normalized)")
            } catch {
                throw ConfigurationError.invalidDataDirectory("Cannot create directory: \(error.localizedDescription)")
            }
        }
        
        // Check if directory is writable
        guard FileManager.default.isWritableFile(atPath: normalized) else {
            throw ConfigurationError.invalidDataDirectory("Directory is not writable: \(normalized)")
        }
    }
    
    private static func validateSSLFile(_ path: String, type: String) throws {
        // Check path traversal
        let normalized = (path as NSString).standardizingPath
        if normalized.contains("..") {
            throw ConfigurationError.invalidSSLPath("SSL \(type) path contains '..'")
        }
        
        // Check file exists
        guard FileManager.default.fileExists(atPath: normalized) else {
            if type == "certificate" {
                throw ConfigurationError.sslCertificateNotFound(normalized)
            } else {
                throw ConfigurationError.sslPrivateKeyNotFound(normalized)
            }
        }
        
        // Check file is readable
        guard FileManager.default.isReadableFile(atPath: normalized) else {
            throw ConfigurationError.invalidSSLPath("SSL \(type) file is not readable: \(normalized)")
        }
    }
    
    private static func checkSSLFilePermissions(_ certPath: String, _ keyPath: String) {
        // Check private key permissions (should be restrictive)
        do {
            let attrs = try FileManager.default.attributesOfItem(atPath: keyPath)
            if let posixPerms = attrs[.posixPermissions] as? NSNumber {
                let perms = posixPerms.uint16Value
                // Check if world-readable or group-readable
                if (perms & 0o044) != 0 {
                    print("⚠️  Security Warning: SSL private key has overly permissive file permissions")
                    print("   Recommended: chmod 600 \(keyPath)")
                }
            }
        } catch {
            // Can't check permissions, skip warning
        }
    }
}

// MARK: - Configuration Errors

public enum ConfigurationError: Error, LocalizedError {
    case invalidHost(String)
    case invalidPort(Int)
    case invalidMaxConnections(Int)
    case invalidDataDirectory(String)
    case sslConfigurationIncomplete
    case sslCertificateNotFound(String)
    case sslPrivateKeyNotFound(String)
    case invalidSSLPath(String)
    case invalidConnectionTimeout(TimeInterval)
    case invalidQueryTimeout(TimeInterval)
    
    public var errorDescription: String? {
        switch self {
        case .invalidHost(let message):
            return "Invalid host configuration: \(message)"
        case .invalidPort(let port):
            return "Invalid port number: \(port). Port must be between 1 and 65535."
        case .invalidMaxConnections(let max):
            return "Invalid max connections: \(max). Must be between 1 and 100000."
        case .invalidDataDirectory(let message):
            return "Invalid data directory: \(message)"
        case .sslConfigurationIncomplete:
            return "SSL is enabled but certificate or private key path is missing."
        case .sslCertificateNotFound(let path):
            return "SSL certificate file not found: \(path)"
        case .sslPrivateKeyNotFound(let path):
            return "SSL private key file not found: \(path)"
        case .invalidSSLPath(let message):
            return "Invalid SSL file path: \(message)"
        case .invalidConnectionTimeout(let timeout):
            return "Invalid connection timeout: \(timeout). Timeout must be between 0 and 3600 seconds."
        case .invalidQueryTimeout(let timeout):
            return "Invalid query timeout: \(timeout). Timeout must be between 0 and 3600 seconds."
        }
    }
}
