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
        print("ColibrìDB Server")
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
        // Validate port
        guard config.port > 0 && config.port <= 65535 else {
            throw ConfigurationError.invalidPort(config.port)
        }
        
        // Validate data directory
        let dataDir = URL(fileURLWithPath: config.dataDirectory)
        if !FileManager.default.fileExists(atPath: config.dataDirectory) {
            try FileManager.default.createDirectory(at: dataDir, withIntermediateDirectories: true)
        }
        
        // Validate SSL configuration
        if config.sslEnabled {
            guard let certPath = config.sslCertificatePath,
                  let keyPath = config.sslPrivateKeyPath else {
                throw ConfigurationError.sslConfigurationIncomplete
            }
            
            guard FileManager.default.fileExists(atPath: certPath) else {
                throw ConfigurationError.sslCertificateNotFound(certPath)
            }
            
            guard FileManager.default.fileExists(atPath: keyPath) else {
                throw ConfigurationError.sslPrivateKeyNotFound(keyPath)
            }
        }
        
        // Validate timeouts
        guard config.connectionTimeout > 0 else {
            throw ConfigurationError.invalidConnectionTimeout(config.connectionTimeout)
        }
        
        guard config.queryTimeout > 0 else {
            throw ConfigurationError.invalidQueryTimeout(config.queryTimeout)
        }
    }
}

// MARK: - Configuration Errors

public enum ConfigurationError: Error, LocalizedError {
    case invalidPort(Int)
    case sslConfigurationIncomplete
    case sslCertificateNotFound(String)
    case sslPrivateKeyNotFound(String)
    case invalidConnectionTimeout(TimeInterval)
    case invalidQueryTimeout(TimeInterval)
    
    public var errorDescription: String? {
        switch self {
        case .invalidPort(let port):
            return "Invalid port number: \(port). Port must be between 1 and 65535."
        case .sslConfigurationIncomplete:
            return "SSL is enabled but certificate or private key path is missing."
        case .sslCertificateNotFound(let path):
            return "SSL certificate file not found: \(path)"
        case .sslPrivateKeyNotFound(let path):
            return "SSL private key file not found: \(path)"
        case .invalidConnectionTimeout(let timeout):
            return "Invalid connection timeout: \(timeout). Timeout must be greater than 0."
        case .invalidQueryTimeout(let timeout):
            return "Invalid query timeout: \(timeout). Timeout must be greater than 0."
        }
    }
}
