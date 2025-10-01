//
//  ColibriServer.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: HTTP server for ColibrDB with REST API.

import Foundation
import Network
import os.log

/// HTTP server for ColibrDB
public final class ColibriServer {
    private let logger = Logger(subsystem: "com.colibridb.server", category: "http")
    private let colibriDB: ColibriDB
    private let port: UInt16
    private let host: String
    
    // Network components
    private var listener: NWListener?
    private var connections: Set<NWConnection> = []
    private let connectionQueue = DispatchQueue(label: "com.colibridb.server.connections")
    
    // Server state
    private var isRunning = false
    private let serverLock = NSLock()
    
    // API handlers
    private let apiHandler: APIHandler
    
    public init(colibriDB: ColibriDB, host: String = "localhost", port: UInt16 = 8080) {
        self.colibriDB = colibriDB
        self.host = host
        self.port = port
        self.apiHandler = APIHandler(colibriDB: colibriDB)
    }
    
    /// Starts the HTTP server
    public func start() throws {
        serverLock.lock()
        defer { serverLock.unlock() }
        
        guard !isRunning else {
            logger.warning("Server already running")
            return
        }
        
        logger.info("Starting ColibrDB HTTP server on \(host):\(port)")
        
        do {
            // Create listener
            let parameters = NWParameters.tcp
            parameters.allowLocalEndpointReuse = true
            
            listener = try NWListener(using: parameters, on: NWEndpoint.Port(port)!)
            
            // Set up listener
            listener?.newConnectionHandler = { [weak self] connection in
                self?.handleConnection(connection)
            }
            
            listener?.stateUpdateHandler = { [weak self] state in
                self?.handleListenerState(state)
            }
            
            // Start listening
            listener?.start(queue: connectionQueue)
            
            isRunning = true
            logger.info("ColibrDB HTTP server started successfully")
            
        } catch {
            logger.error("Failed to start HTTP server: \(error.localizedDescription)")
            throw ServerError.startupFailed(error.localizedDescription)
        }
    }
    
    /// Stops the HTTP server
    public func stop() {
        serverLock.lock()
        defer { serverLock.unlock() }
        
        guard isRunning else {
            logger.warning("Server not running")
            return
        }
        
        logger.info("Stopping ColibrDB HTTP server")
        
        // Stop listener
        listener?.cancel()
        listener = nil
        
        // Close all connections
        for connection in connections {
            connection.cancel()
        }
        connections.removeAll()
        
        isRunning = false
        logger.info("ColibrDB HTTP server stopped")
    }
    
    /// Handles new connections
    private func handleConnection(_ connection: NWConnection) {
        connectionQueue.async { [weak self] in
            guard let self = self else { return }
            
            self.connections.insert(connection)
            
            connection.stateUpdateHandler = { [weak self] state in
                self?.handleConnectionState(connection, state: state)
            }
            
            connection.start(queue: self.connectionQueue)
            self.receiveData(on: connection)
        }
    }
    
    /// Handles connection state changes
    private func handleConnectionState(_ connection: NWConnection, state: NWConnection.State) {
        switch state {
        case .ready:
            logger.debug("Connection ready")
        case .failed(let error):
            logger.error("Connection failed: \(error.localizedDescription)")
            connections.remove(connection)
        case .cancelled:
            logger.debug("Connection cancelled")
            connections.remove(connection)
        default:
            break
        }
    }
    
    /// Handles listener state changes
    private func handleListenerState(_ state: NWListener.State) {
        switch state {
        case .ready:
            logger.info("Server listener ready on \(host):\(port)")
        case .failed(let error):
            logger.error("Server listener failed: \(error.localizedDescription)")
        case .cancelled:
            logger.info("Server listener cancelled")
        default:
            break
        }
    }
    
    /// Receives data from connection
    private func receiveData(on connection: NWConnection) {
        connection.receive(minimumIncompleteLength: 1, maximumLength: 65536) { [weak self] data, _, isComplete, error in
            if let data = data, !data.isEmpty {
                self?.handleRequest(data: data, connection: connection)
            }
            
            if isComplete {
                connection.cancel()
            } else if let error = error {
                self?.logger.error("Receive error: \(error.localizedDescription)")
                connection.cancel()
            } else {
                self?.receiveData(on: connection)
            }
        }
    }
    
    /// Handles HTTP requests
    private func handleRequest(data: Data, connection: NWConnection) {
        guard let request = HTTPRequest.parse(data: data) else {
            sendErrorResponse(connection: connection, status: .badRequest, message: "Invalid HTTP request")
            return
        }
        
        logger.debug("Received \(request.method) \(request.path)")
        
        // Route request to API handler
        apiHandler.handleRequest(request) { [weak self] response in
            self?.sendResponse(response, to: connection)
        }
    }
    
    /// Sends HTTP response
    private func sendResponse(_ response: HTTPResponse, to connection: NWConnection) {
        let responseData = response.serialize()
        
        connection.send(content: responseData, completion: .contentProcessed { error in
            if let error = error {
                self.logger.error("Send error: \(error.localizedDescription)")
            }
        })
    }
    
    /// Sends error response
    private func sendErrorResponse(connection: NWConnection, status: HTTPStatus, message: String) {
        let response = HTTPResponse(
            status: status,
            headers: ["Content-Type": "application/json"],
            body: """
            {
                "error": "\(message)",
                "status": \(status.rawValue)
            }
            """
        )
        
        sendResponse(response, to: connection)
    }
    
    /// Gets server status
    public func getStatus() -> ServerStatus {
        serverLock.lock()
        defer { serverLock.unlock() }
        
        return ServerStatus(
            isRunning: isRunning,
            host: host,
            port: port,
            activeConnections: connections.count,
            uptime: Date().timeIntervalSince1970 // This would be calculated from start time
        )
    }
}

/// HTTP request structure
public struct HTTPRequest {
    public let method: HTTPMethod
    public let path: String
    public let headers: [String: String]
    public let body: String
    public let queryParams: [String: String]
    
    public init(method: HTTPMethod, path: String, headers: [String: String] = [:], body: String = "", queryParams: [String: String] = [:]) {
        self.method = method
        self.path = path
        self.headers = headers
        self.body = body
        self.queryParams = queryParams
    }
    
    /// Parses HTTP request from data
    public static func parse(data: Data) -> HTTPRequest? {
        guard let requestString = String(data: data, encoding: .utf8) else { return nil }
        
        let lines = requestString.components(separatedBy: "\r\n")
        guard !lines.isEmpty else { return nil }
        
        // Parse request line
        let requestLine = lines[0].components(separatedBy: " ")
        guard requestLine.count >= 3 else { return nil }
        
        let method = HTTPMethod(rawValue: requestLine[0]) ?? .GET
        let pathWithQuery = requestLine[1]
        
        // Parse path and query parameters
        let pathComponents = pathWithQuery.components(separatedBy: "?")
        let path = pathComponents[0]
        let queryParams = pathComponents.count > 1 ? parseQueryParams(pathComponents[1]) : [:]
        
        // Parse headers
        var headers: [String: String] = [:]
        var bodyStartIndex = 1
        
        for (index, line) in lines.enumerated() {
            if line.isEmpty {
                bodyStartIndex = index + 1
                break
            }
            if index > 0 {
                let headerComponents = line.components(separatedBy: ": ")
                if headerComponents.count == 2 {
                    headers[headerComponents[0].lowercased()] = headerComponents[1]
                }
            }
        }
        
        // Parse body
        let body = lines.suffix(from: bodyStartIndex).joined(separator: "\r\n")
        
        return HTTPRequest(
            method: method,
            path: path,
            headers: headers,
            body: body,
            queryParams: queryParams
        )
    }
    
    /// Parses query parameters
    private static func parseQueryParams(_ queryString: String) -> [String: String] {
        var params: [String: String] = [:]
        
        for param in queryString.components(separatedBy: "&") {
            let components = param.components(separatedBy: "=")
            if components.count == 2 {
                params[components[0]] = components[1].removingPercentEncoding ?? components[1]
            }
        }
        
        return params
    }
}

/// HTTP response structure
public struct HTTPResponse {
    public let status: HTTPStatus
    public let headers: [String: String]
    public let body: String
    
    public init(status: HTTPStatus, headers: [String: String] = [:], body: String = "") {
        self.status = status
        self.headers = headers
        self.body = body
    }
    
    /// Serializes response to data
    public func serialize() -> Data {
        var response = "HTTP/1.1 \(status.rawValue) \(status.description)\r\n"
        
        // Add headers
        for (key, value) in headers {
            response += "\(key): \(value)\r\n"
        }
        
        // Add content length
        let bodyData = body.data(using: .utf8) ?? Data()
        response += "Content-Length: \(bodyData.count)\r\n"
        
        // Add connection close
        response += "Connection: close\r\n"
        
        // Add empty line
        response += "\r\n"
        
        // Add body
        response += body
        
        return response.data(using: .utf8) ?? Data()
    }
}

/// HTTP methods
public enum HTTPMethod: String {
    case GET = "GET"
    case POST = "POST"
    case PUT = "PUT"
    case DELETE = "DELETE"
    case PATCH = "PATCH"
    case HEAD = "HEAD"
    case OPTIONS = "OPTIONS"
}

/// HTTP status codes
public enum HTTPStatus: Int {
    case ok = 200
    case created = 201
    case noContent = 204
    case badRequest = 400
    case unauthorized = 401
    case forbidden = 403
    case notFound = 404
    case methodNotAllowed = 405
    case internalServerError = 500
    case serviceUnavailable = 503
    
    public var description: String {
        switch self {
        case .ok: return "OK"
        case .created: return "Created"
        case .noContent: return "No Content"
        case .badRequest: return "Bad Request"
        case .unauthorized: return "Unauthorized"
        case .forbidden: return "Forbidden"
        case .notFound: return "Not Found"
        case .methodNotAllowed: return "Method Not Allowed"
        case .internalServerError: return "Internal Server Error"
        case .serviceUnavailable: return "Service Unavailable"
        }
    }
}

/// Server status
public struct ServerStatus {
    public let isRunning: Bool
    public let host: String
    public let port: UInt16
    public let activeConnections: Int
    public let uptime: TimeInterval
    
    public init(isRunning: Bool, host: String, port: UInt16, activeConnections: Int, uptime: TimeInterval) {
        self.isRunning = isRunning
        self.host = host
        self.port = port
        self.activeConnections = activeConnections
        self.uptime = uptime
    }
}

/// Server errors
public enum ServerError: Error, LocalizedError {
    case startupFailed(String)
    case invalidRequest(String)
    case internalError(String)
    case serviceUnavailable(String)
    
    public var errorDescription: String? {
        switch self {
        case .startupFailed(let message):
            return "Server startup failed: \(message)"
        case .invalidRequest(let message):
            return "Invalid request: \(message)"
        case .internalError(let message):
            return "Internal server error: \(message)"
        case .serviceUnavailable(let message):
            return "Service unavailable: \(message)"
        }
    }
}