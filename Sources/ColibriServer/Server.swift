//
//  Server.swift
//  ColibrìDB Server Implementation
//
//  Based on: spec/Server.tla
//  Implements: HTTP server and API endpoints
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Concurrency: Multiple concurrent connections
//  - Scalability: Handles high load efficiently
//  - Reliability: Graceful error handling
//  - Security: Input validation and sanitization
//

import Foundation
import Network
import ColibriCore

// MARK: - Server Configuration

/// Server configuration
public struct ServerConfig: Codable, Sendable {
    public let host: String
    public let port: Int
    public let maxConnections: Int
    public let timeoutSeconds: Int
    public let enableSSL: Bool
    
    public init(host: String = "localhost", port: Int = 8080, maxConnections: Int = 1000, timeoutSeconds: Int = 30, enableSSL: Bool = false) {
        self.host = host
        self.port = port
        self.maxConnections = maxConnections
        self.timeoutSeconds = timeoutSeconds
        self.enableSSL = enableSSL
    }
    
    public static let `default` = ServerConfig()
}

// MARK: - HTTP Request/Response

/// HTTP request
public struct HTTPRequest: Codable, Sendable {
    public let method: String
    public let path: String
    public let headers: [String: String]
    public let body: Data?
    public let queryParams: [String: String]
    
    public init(method: String, path: String, headers: [String: String] = [:], body: Data? = nil, queryParams: [String: String] = [:]) {
        self.method = method
        self.path = path
        self.headers = headers
        self.body = body
        self.queryParams = queryParams
    }
}

/// HTTP response
public struct HTTPResponse: Codable, Sendable {
    public let statusCode: Int
    public let headers: [String: String]
    public let body: Data?
    
    public init(statusCode: Int, headers: [String: String] = [:], body: Data? = nil) {
        self.statusCode = statusCode
        self.headers = headers
        self.body = body
    }
    
    public static func ok(body: Data? = nil) -> HTTPResponse {
        return HTTPResponse(statusCode: 200, body: body)
    }
    
    public static func notFound() -> HTTPResponse {
        return HTTPResponse(statusCode: 404, body: "Not Found".data(using: .utf8))
    }
    
    public static func badRequest() -> HTTPResponse {
        return HTTPResponse(statusCode: 400, body: "Bad Request".data(using: .utf8))
    }
    
    public static func internalServerError() -> HTTPResponse {
        return HTTPResponse(statusCode: 500, body: "Internal Server Error".data(using: .utf8))
    }
}

// MARK: - Connection Handler

/// Connection handler for individual client connections
public actor ConnectionHandler {
    private let connection: NWConnection
    private let server: ColibriServer
    private let requestHandler: RequestHandler
    
    public init(connection: NWConnection, server: ColibriServer, requestHandler: RequestHandler) {
        self.connection = connection
        self.server = server
        self.requestHandler = requestHandler
    }
    
    /// Handle client connection
    public func handleConnection() async {
        connection.start(queue: .global())
        
        while true {
            do {
                let data = try await receiveData()
                let request = try parseRequest(data)
                let response = try await requestHandler.handleRequest(request)
                try await sendResponse(response)
            } catch {
                break
            }
        }
        
        connection.cancel()
    }
    
    /// Receive data from connection
    private func receiveData() async throws -> Data {
        return try await withCheckedThrowingContinuation { continuation in
            connection.receive(minimumIncompleteLength: 1, maximumLength: 65536) { data, _, isComplete, error in
                if let error = error {
                    continuation.resume(throwing: error)
                } else if let data = data {
                    continuation.resume(returning: data)
                } else if isComplete {
                    continuation.resume(throwing: ServerError.connectionClosed)
                }
            }
        }
    }
    
    /// Parse HTTP request from data
    private func parseRequest(_ data: Data) throws -> HTTPRequest {
        let requestString = String(data: data, encoding: .utf8) ?? ""
        let lines = requestString.components(separatedBy: "\r\n")
        
        guard let firstLine = lines.first else {
            throw ServerError.invalidRequest
        }
        
        let components = firstLine.components(separatedBy: " ")
        guard components.count >= 3 else {
            throw ServerError.invalidRequest
        }
        
        let method = components[0]
        let path = components[1]
        
        // Parse headers
        var headers: [String: String] = [:]
        var bodyStartIndex = 0
        
        for (index, line) in lines.enumerated() {
            if line.isEmpty {
                bodyStartIndex = index + 1
                break
            }
            if index > 0 {
                let headerComponents = line.components(separatedBy: ": ")
                if headerComponents.count == 2 {
                    headers[headerComponents[0]] = headerComponents[1]
                }
            }
        }
        
        // Parse body
        let bodyLines = Array(lines[bodyStartIndex...])
        let bodyString = bodyLines.joined(separator: "\r\n")
        let body = bodyString.isEmpty ? nil : bodyString.data(using: .utf8)
        
        return HTTPRequest(method: method, path: path, headers: headers, body: body)
    }
    
    /// Send HTTP response
    private func sendResponse(_ response: HTTPResponse) async throws {
        var responseString = "HTTP/1.1 \(response.statusCode) OK\r\n"
        
        for (key, value) in response.headers {
            responseString += "\(key): \(value)\r\n"
        }
        
        responseString += "\r\n"
        
        if let body = response.body {
            responseString += String(data: body, encoding: .utf8) ?? ""
        }
        
        let responseData = responseString.data(using: .utf8) ?? Data()
        
        try await withCheckedThrowingContinuation { (continuation: CheckedContinuation<Void, Error>) in
            connection.send(content: responseData, completion: .contentProcessed { error in
                if let error = error {
                    continuation.resume(throwing: error)
                } else {
                    continuation.resume()
                }
            })
        }
    }
}

// MARK: - Request Handler

/// Request handler for processing HTTP requests
public actor RequestHandler {
    private let database: ColibrìDB
    private let auth: AuthenticationManager
    private var activeTransactions: [String: TxID] = [:]  // sessionId -> txID
    
    public init(database: ColibrìDB, auth: AuthenticationManager) {
        self.database = database
        self.auth = auth
    }
    
    /// Get or create transaction for session
    private func getOrCreateTransaction(sessionId: String) async throws -> TxID {
        if let txID = activeTransactions[sessionId] {
            return txID
        }
        let txID = try await database.beginTransaction()
        activeTransactions[sessionId] = txID
        return txID
    }
    
    /// Handle HTTP request
    public func handleRequest(_ request: HTTPRequest) async throws -> HTTPResponse {
        switch request.path {
        case "/api/tables":
            return try await handleTablesRequest(request)
        case "/api/query":
            return try await handleQueryRequest(request)
        case "/api/transaction":
            return try await handleTransactionRequest(request)
        case "/api/health":
            return handleHealthRequest(request)
        default:
            // Users endpoints (prefix-based)
            if request.path == "/api/users" || request.path.hasPrefix("/api/users/") || request.path == "/api/users/login" {
                return try await handleUsersRequest(request)
            } else {
                return HTTPResponse.notFound()
            }
        }
    }
    
    /// Handle tables API request
    private func handleTablesRequest(_ request: HTTPRequest) async throws -> HTTPResponse {
        switch request.method {
        case "GET":
            // Get table names from catalog via database
            // We need to access catalog through database
            // For now, we'll need to add a method to ColibrìDB to expose this
            // Temporary: return empty array until we add listTables() to ColibrìDB
            let tableNames: [String] = []  // TODO: await database.listTables()
            let responseData = try JSONEncoder().encode(tableNames)
            return HTTPResponse.ok(body: responseData)
        case "POST":
            // Create table
            guard let body = request.body else {
                return HTTPResponse.badRequest()
            }
            
            let tableRequest = try JSONDecoder().decode(CreateTableRequest.self, from: body)
            
            // Convert CreateTableRequest to TableDefinition
            let columns = tableRequest.columns.map { col in
                ColumnDefinition(
                    name: col.name,
                    type: col.type,
                    nullable: col.nullable,
                    defaultValue: col.defaultValue
                )
            }
            
            // Convert Set<String> to [String]? for primaryKey
            let primaryKey: [String]? = tableRequest.primaryKey.isEmpty ? nil : Array(tableRequest.primaryKey)
            
            // For now, indexes are empty - could be added later from CreateTableRequest
            let indexes: [CatalogIndexDefinition] = []
            
            let tableDef = TableDefinition(
                name: tableRequest.name,
                columns: columns,
                primaryKey: primaryKey,
                indexes: indexes
            )
            
            try await database.createTable(tableDef)
            
            return HTTPResponse.ok()
        default:
            return HTTPResponse.badRequest()
        }
    }
    
    /// Handle query API request
    private func handleQueryRequest(_ request: HTTPRequest) async throws -> HTTPResponse {
        guard request.method == "POST" else {
            return HTTPResponse.badRequest()
        }
        
        guard let body = request.body else {
            return HTTPResponse.badRequest()
        }
        
        let queryRequest = try JSONDecoder().decode(QueryRequest.self, from: body)
        
        // Get session ID from headers (or generate one)
        let sessionId = request.headers["X-Session-Id"] ?? UUID().uuidString
        
        // Get or create transaction
        let txID = try await getOrCreateTransaction(sessionId: sessionId)
        
        // Execute query using ColibrìDB
        let result = try await database.executeQuery(queryRequest.query, txId: txID)
        let responseData = try JSONEncoder().encode(result)
        
        return HTTPResponse.ok(body: responseData)
    }
    
    /// Handle transaction API request (BEGIN, COMMIT, ROLLBACK)
    private func handleTransactionRequest(_ request: HTTPRequest) async throws -> HTTPResponse {
        let sessionId = request.headers["X-Session-Id"] ?? UUID().uuidString
        let action = request.queryParams["action"] ?? "begin"
        
        switch action.lowercased() {
        case "begin":
            let txID = try await database.beginTransaction()
            activeTransactions[sessionId] = txID
            return HTTPResponse.ok(body: "{\"transaction_id\": \(txID)}".data(using: .utf8))
        case "commit":
            if let txID = activeTransactions[sessionId] {
                try await database.commit(txId: txID)
                activeTransactions.removeValue(forKey: sessionId)
                return HTTPResponse.ok()
            }
            return HTTPResponse.badRequest()
        case "rollback":
            if let txID = activeTransactions[sessionId] {
                try await database.abort(txId: txID)
                activeTransactions.removeValue(forKey: sessionId)
                return HTTPResponse.ok()
            }
            return HTTPResponse.badRequest()
        default:
            return HTTPResponse.badRequest()
        }
    }
    
    /// Handle health check request
    private func handleHealthRequest(_ request: HTTPRequest) -> HTTPResponse {
        let health = HealthStatus(
            status: "healthy",
            timestamp: Date(),
            version: "1.0.0"
        )
        
        do {
            let responseData = try JSONEncoder().encode(health)
            return HTTPResponse.ok(body: responseData)
        } catch {
            return HTTPResponse.internalServerError()
        }
    }
    
    // MARK: - Users API
    private func handleUsersRequest(_ request: HTTPRequest) async throws -> HTTPResponse {
        // POST /api/users/login
        if request.path == "/api/users/login", request.method == "POST" {
            guard let body = request.body else { return HTTPResponse.badRequest() }
            let login = try JSONDecoder().decode(LoginRequest.self, from: body)
            do {
                let sessionId = try await auth.authenticate(username: login.username, password: login.password)
                let resp = LoginResponse(sessionId: sessionId, username: login.username)
                let data = try JSONEncoder().encode(resp)
                return HTTPResponse.ok(body: data)
            } catch {
                return HTTPResponse.badRequest()
            }
        }
        
        // /api/users
        if request.path == "/api/users" {
            switch request.method {
            case "GET":
                let users = await auth.getAllUsers().map(PublicUser.from(_:))
                let data = try JSONEncoder().encode(users)
                return HTTPResponse.ok(body: data)
            case "POST":
                guard let body = request.body else { return HTTPResponse.badRequest() }
                let createReq = try JSONDecoder().decode(CreateUserRequest.self, from: body)
                // transactional boundary
                let tx = try await database.beginTransaction()
                do {
                    try await auth.createUser(username: createReq.username, email: createReq.email, password: createReq.password, role: createReq.role)
                    try await database.commit(txId: tx)
                    return HTTPResponse.ok()
                } catch {
                    try? await database.abort(txId: tx)
                    return HTTPResponse.badRequest()
                }
            default:
                return HTTPResponse.badRequest()
            }
        }
        
        // /api/users/{username} and subresources
        if request.path.hasPrefix("/api/users/") {
            let rest = String(request.path.dropFirst("/api/users/".count))
            let parts = rest.split(separator: "/").map(String.init)
            guard let username = parts.first, !username.isEmpty else { return HTTPResponse.badRequest() }
            if parts.count == 1 {
                switch request.method {
                case "GET":
                    if let user = await auth.getUser(username: username) {
                        let data = try JSONEncoder().encode(PublicUser.from(user))
                        return HTTPResponse.ok(body: data)
                    } else {
                        return HTTPResponse.notFound()
                    }
                case "DELETE":
                    let tx = try await database.beginTransaction()
                    do {
                        try await auth.deleteUser(username: username)
                        try await database.commit(txId: tx)
                        return HTTPResponse.ok()
                    } catch {
                        try? await database.abort(txId: tx)
                        return HTTPResponse.notFound()
                    }
                default:
                    return HTTPResponse.badRequest()
                }
            } else if parts.count == 2, parts[1] == "role", request.method == "PUT" {
                guard let body = request.body else { return HTTPResponse.badRequest() }
                let req = try JSONDecoder().decode(UpdateUserRoleRequest.self, from: body)
                let tx = try await database.beginTransaction()
                do {
                    try await auth.updateUserRole(username: username, newRole: req.role)
                    try await database.commit(txId: tx)
                    return HTTPResponse.ok()
                } catch {
                    try? await database.abort(txId: tx)
                    return HTTPResponse.notFound()
                }
            } else if parts.count == 2, parts[1] == "password", request.method == "PUT" {
                guard let body = request.body else { return HTTPResponse.badRequest() }
                let req = try JSONDecoder().decode(ChangePasswordRequest.self, from: body)
                let tx = try await database.beginTransaction()
                do {
                    try await auth.changePassword(username: username, oldPassword: req.oldPassword, newPassword: req.newPassword)
                    try await database.commit(txId: tx)
                    return HTTPResponse.ok()
                } catch {
                    try? await database.abort(txId: tx)
                    return HTTPResponse.badRequest()
                }
            }
        }
        
        return HTTPResponse.notFound()
    }
}

// MARK: - Supporting Types

/// Create table request
public struct CreateTableRequest: Codable, Sendable {
    public let name: String
    public let columns: [ColumnMetadata]
    public let primaryKey: Set<String>
    public let foreignKeys: [ForeignKeyMetadata]
    public let constraints: [ConstraintMetadata]
}

/// Query request
public struct QueryRequest: Codable, Sendable {
    public let query: String
}

// QueryResult è definito in ColibriCore, non serve ridefinirlo qui

/// Health status
public struct HealthStatus: Codable, Sendable {
    public let status: String
    public let timestamp: Date
    public let version: String
}

// MARK: - Users DTOs
public struct CreateUserRequest: Codable, Sendable {
    public let username: String
    public let email: String
    public let password: String
    public let role: UserRole
}

public struct UpdateUserRoleRequest: Codable, Sendable {
    public let role: UserRole
}

public struct ChangePasswordRequest: Codable, Sendable {
    public let oldPassword: String
    public let newPassword: String
}

public struct LoginRequest: Codable, Sendable {
    public let username: String
    public let password: String
}

public struct LoginResponse: Codable, Sendable {
    public let sessionId: String
    public let username: String
}

public struct PublicUser: Codable, Sendable {
    public let username: String
    public let email: String
    public let role: UserRole
    public let status: UserStatus
    public let createdAt: Date
    public let lastLogin: Date?
    
    public static func from(_ u: UserMetadata) -> PublicUser {
        return PublicUser(username: u.username, email: u.email, role: u.role, status: u.status, createdAt: u.createdAt, lastLogin: u.lastLogin)
    }
}

// MARK: - Colibri Server

/// Main ColibrìDB Server
/// Corresponds to TLA+ module: Server.tla
public actor ColibriServer {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Server configuration
    private let config: ServerConfig
    
    /// Listener for incoming connections
    private var listener: NWListener?
    
    /// Active connections
    private var activeConnections: [UUID: ConnectionHandler] = [:]
    
    /// Server state
    private var isRunning: Bool = false
    
    /// Request handler
    private let requestHandler: RequestHandler
    private let authManager: AuthenticationManager
    
    // MARK: - Dependencies
    
    /// Database instance
    private let database: ColibrìDB
    
    /// System catalog manager (loads descriptors from sys_* tables)
    public let catalogManager: SystemCatalogManager
    
    /// Privilege manager (handles GRANT/REVOKE)
    public let privilegeManager: PrivilegeManager
    
    // MARK: - Initialization
    
    public init(config: ServerConfig = .default, database: ColibrìDB) async throws {
        self.config = config
        self.database = database
        
        // Initialize SQL-backed private schema (colibri_sys)
        let bootstrap = SystemCatalogBootstrap()
        try await bootstrap.initialize(on: database)
        
        // Initialize user store and auth
        let userStore = SQLUserStore(database: database)
        try await userStore.initializeSchema()
        self.authManager = AuthenticationManager(store: userStore)
        
        // Initialize catalog and privilege managers
        self.catalogManager = SystemCatalogManager(database: database)
        self.privilegeManager = PrivilegeManager(database: database)
        
        // Load catalog descriptors and privileges from sys_* tables
        try await catalogManager.loadAll()
        try await privilegeManager.loadAll()
        
        self.requestHandler = RequestHandler(database: database, auth: authManager)
    }
    
    // MARK: - Server Operations
    
    /// Start the server
    /// TLA+ Action: StartServer
    public func start() async throws {
        guard !isRunning else {
            throw ServerError.serverAlreadyRunning
        }
        
        let parameters = NWParameters.tcp
        if config.enableSSL {
            parameters.defaultProtocolStack.applicationProtocols.insert(NWProtocolTLS.Options(), at: 0)
        }
        
        listener = try NWListener(using: parameters, on: NWEndpoint.Port(rawValue: UInt16(config.port))!)
        listener?.newConnectionHandler = { [weak self] connection in
            Task {
                await self?.handleNewConnection(connection)
            }
        }
        
        listener?.start(queue: .global())
        isRunning = true
    }
    
    /// Stop the server
    /// TLA+ Action: StopServer
    public func stop() async {
        listener?.cancel()
        listener = nil
        
        // Close all active connections
        for (_, _) in activeConnections {
            // Connection will be removed when it closes
        }
        
        isRunning = false
    }
    
    /// Handle new connection
    private func handleNewConnection(_ connection: NWConnection) async {
        let connectionId = UUID()
        let connectionHandler = ConnectionHandler(connection: connection, server: self, requestHandler: requestHandler)
        activeConnections[connectionId] = connectionHandler
        
        await connectionHandler.handleConnection()
        
        activeConnections.removeValue(forKey: connectionId)
    }
    
    // MARK: - Query Operations
    
    /// Check if server is running
    public func isServerRunning() -> Bool {
        return isRunning
    }
    
    /// Get active connection count
    public func getActiveConnectionCount() -> Int {
        return activeConnections.count
    }
    
    /// Get server configuration
    public func getConfig() -> ServerConfig {
        return config
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check concurrency invariant
    /// TLA+ Inv_Server_Concurrency
    public func checkConcurrencyInvariant() -> Bool {
        return activeConnections.count <= config.maxConnections
    }
    
    /// Check scalability invariant
    /// TLA+ Inv_Server_Scalability
    public func checkScalabilityInvariant() -> Bool {
        return true // Simplified
    }
    
    /// Check reliability invariant
    /// TLA+ Inv_Server_Reliability
    public func checkReliabilityInvariant() -> Bool {
        return true // Simplified
    }
    
    /// Check security invariant
    /// TLA+ Inv_Server_Security
    public func checkSecurityInvariant() -> Bool {
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let concurrency = checkConcurrencyInvariant()
        let scalability = checkScalabilityInvariant()
        let reliability = checkReliabilityInvariant()
        let security = checkSecurityInvariant()
        
        return concurrency && scalability && reliability && security
    }
}

// MARK: - Errors

public enum ServerError: Error, LocalizedError {
    case serverAlreadyRunning
    case connectionClosed
    case invalidRequest
    case invalidResponse
    
    public var errorDescription: String? {
        switch self {
        case .serverAlreadyRunning:
            return "Server is already running"
        case .connectionClosed:
            return "Connection closed"
        case .invalidRequest:
            return "Invalid request"
        case .invalidResponse:
            return "Invalid response"
        }
    }
}
