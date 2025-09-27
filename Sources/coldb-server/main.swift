#!/usr/bin/env swift

//
//  main.swift
//  coldb-server
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: ColibrìDB Network Server - High-performance database server with SwiftNIO

import Foundation
import NIO
import NIOHTTP1
import NIOSSL
import ColibriCore

// MARK: - Database Server

final class DatabaseServer {
    private let config: ServerConfiguration
    private let database: Database
    private let group: EventLoopGroup
    private let connectionManager: ConnectionManager
    private var serverChannel: Channel?
    
    init(config: ServerConfiguration) throws {
        self.config = config
        
        // Initialize database
        let dbConfig = DBConfig(dataDir: config.dataDirectory)
        self.database = Database(config: dbConfig)
        
        // Initialize event loop group
        self.group = MultiThreadedEventLoopGroup(numberOfThreads: System.coreCount)
        
        // Initialize connection manager
        self.connectionManager = ConnectionManager(
            maxConnections: config.maxConnections,
            connectionTimeout: config.connectionTimeout,
            queryTimeout: config.queryTimeout,
            database: database
        )
    }
    
    func start() throws {
        print("🚀 Starting ColibrìDB Server...")
        print("📊 Database: \(config.dataDirectory)")
        print("🌐 Server: \(config.host):\(config.port)")
        print("🔒 SSL: \(config.sslEnabled ? "Enabled" : "Disabled")")
        print("🔗 Max Connections: \(config.maxConnections)")
        
        let bootstrap = ServerBootstrap(group: group)
            .serverChannelOption(ChannelOptions.backlog, value: 256)
            .serverChannelOption(ChannelOptions.socket(SocketOptionLevel(SOL_SOCKET), SO_REUSEADDR), value: 1)
            .childChannelInitializer { channel in
                if self.config.sslEnabled {
                    return self.configureSSL(channel: channel)
                } else {
                    return self.configureHTTP(channel: channel)
                }
            }
            .childChannelOption(ChannelOptions.socket(IPPROTO_TCP, TCP_NODELAY), value: 1)
            .childChannelOption(ChannelOptions.socket(SocketOptionLevel(SOL_SOCKET), SO_REUSEADDR), value: 1)
            .childChannelOption(ChannelOptions.maxMessagesPerRead, value: 16)
            .childChannelOption(ChannelOptions.recvAllocator, value: AdaptiveRecvByteBufferAllocator())
        
        do {
            let channel = try bootstrap.bind(host: config.host, port: config.port).wait()
            self.serverChannel = channel
            
            print("✅ Server started successfully on \(config.host):\(config.port)")
            
            // Wait for server to close
            try channel.closeFuture.wait()
        } catch {
            print("❌ Failed to start server: \(error)")
            throw error
        }
    }
    
    func stop() throws {
        print("🛑 Stopping ColibrìDB Server...")
        
        if let channel = serverChannel {
            try channel.close().wait()
        }
        
        try group.syncShutdownGracefully()
        print("✅ Server stopped successfully")
    }
    
    private func configureSSL(channel: Channel) -> EventLoopFuture<Void> {
        guard let certPath = config.sslCertificatePath,
              let keyPath = config.sslPrivateKeyPath else {
            return channel.eventLoop.makeFailedFuture(ServerError.sslConfigurationMissing)
        }
        
        do {
            let sslContext = try NIOSSLContext(
                configuration: TLSConfiguration.makeServerConfiguration(
                    certificateChain: try NIOSSLCertificate.fromPEMFile(certPath).map { .certificate($0) },
                    privateKey: .file(keyPath)
                )
            )
            
            let sslHandler = NIOSSLServerHandler(context: sslContext)
            return channel.pipeline.addHandler(sslHandler).flatMap {
                self.configureHTTP(channel: channel)
            }
        } catch {
            return channel.eventLoop.makeFailedFuture(error)
        }
    }
    
    private func configureHTTP(channel: Channel) -> EventLoopFuture<Void> {
        return channel.pipeline.addHandler(HTTPRequestHandler(database: database))
    }
}

// MARK: - HTTP Request Handler

final class HTTPRequestHandler: ChannelInboundHandler {
    typealias InboundIn = HTTPServerRequestPart
    typealias OutboundOut = HTTPServerResponsePart
    
    private let database: Database
    private var requestBuffer: HTTPRequestBuffer
    
    init(database: Database) {
        self.database = database
        self.requestBuffer = HTTPRequestBuffer()
    }
    
    func channelRead(context: ChannelHandlerContext, data: NIOAny) {
        let requestPart = unwrapInboundIn(data)
        
        switch requestPart {
        case .head(let head):
            requestBuffer.processHead(head)
        case .body(let body):
            requestBuffer.processBody(body)
        case .end:
            handleRequest(context: context, request: requestBuffer.buildRequest())
            requestBuffer = HTTPRequestBuffer()
        }
    }
    
    private func handleRequest(context: ChannelHandlerContext, request: HTTPRequest) {
        let response = processRequest(request)
        sendResponse(context: context, response: response)
    }
    
    private func processRequest(_ request: HTTPRequest) -> HTTPResponse {
        let path = request.head.uri
        let method = request.head.method
        
        switch (method, path) {
        case (.GET, "/health"):
            return HTTPResponse(
                head: HTTPResponseHead(
                    version: .http1_1,
                    status: .ok,
                    headers: ["Content-Type": "application/json"]
                ),
                body: Data("{\"status\":\"healthy\",\"database\":\"connected\"}".utf8)
            )
            
        case (.POST, "/query"):
            return handleSQLQuery(request)
            
        case (.GET, "/tables"):
            return handleListTables()
            
        case (.POST, "/tables"):
            return handleCreateTable(request)
            
        case (.GET, let path) where path.hasPrefix("/tables/"):
            let tableName = String(path.dropFirst(8)) // Remove "/tables/"
            return handleTableInfo(tableName: tableName)
            
        default:
            return HTTPResponse(
                head: HTTPResponseHead(
                    version: .http1_1,
                    status: .notFound,
                    headers: ["Content-Type": "application/json"]
                ),
                body: Data("{\"error\":\"Not Found\"}".utf8)
            )
        }
    }
    
    private func handleSQLQuery(_ request: HTTPRequest) -> HTTPResponse {
        guard let body = request.body,
              let queryData = String(data: body, encoding: .utf8) else {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .badRequest),
                body: Data("{\"error\":\"Invalid request body\"}".utf8)
            )
        }
        
        do {
            let interface = SQLQueryInterface(database: database)
            let result = try interface.execute(queryData)
            
            let responseData = try JSONEncoder().encode(result)
            return HTTPResponse(
                head: HTTPResponseHead(
                    version: .http1_1,
                    status: .ok,
                    headers: ["Content-Type": "application/json"]
                ),
                body: responseData
            )
        } catch {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .internalServerError),
                body: Data("{\"error\":\"\(error.localizedDescription)\"}".utf8)
            )
        }
    }
    
    private func handleListTables() -> HTTPResponse {
        do {
            let tables = database.listTables()
            let responseData = try JSONEncoder().encode(["tables": tables])
            return HTTPResponse(
                head: HTTPResponseHead(
                    version: .http1_1,
                    status: .ok,
                    headers: ["Content-Type": "application/json"]
                ),
                body: responseData
            )
        } catch {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .internalServerError),
                body: Data("{\"error\":\"\(error.localizedDescription)\"}".utf8)
            )
        }
    }
    
    private func handleCreateTable(_ request: HTTPRequest) -> HTTPResponse {
        guard let body = request.body,
              let tableName = String(data: body, encoding: .utf8) else {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .badRequest),
                body: Data("{\"error\":\"Table name required\"}".utf8)
            )
        }
        
        do {
            try database.createTable(tableName)
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .created),
                body: Data("{\"message\":\"Table '\(tableName)' created\"}".utf8)
            )
        } catch {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .internalServerError),
                body: Data("{\"error\":\"\(error.localizedDescription)\"}".utf8)
            )
        }
    }
    
    private func handleTableInfo(tableName: String) -> HTTPResponse {
        do {
            let rows = try database.scan(tableName)
            let responseData = try JSONEncoder().encode(["table": tableName, "rows": rows.count])
            return HTTPResponse(
                head: HTTPResponseHead(
                    version: .http1_1,
                    status: .ok,
                    headers: ["Content-Type": "application/json"]
                ),
                body: responseData
            )
        } catch {
            return HTTPResponse(
                head: HTTPResponseHead(version: .http1_1, status: .internalServerError),
                body: Data("{\"error\":\"\(error.localizedDescription)\"}".utf8)
            )
        }
    }
    
    private func sendResponse(context: ChannelHandlerContext, response: HTTPResponse) {
        let head = response.head
        let body = response.body
        
        context.write(wrapOutboundOut(.head(head)), promise: nil)
        
        if !body.isEmpty {
            var buffer = context.channel.allocator.buffer(capacity: body.count)
            buffer.writeBytes(body)
            context.write(wrapOutboundOut(.body(.byteBuffer(buffer))), promise: nil)
        }
        
        context.writeAndFlush(wrapOutboundOut(.end(nil)), promise: nil)
    }
}

// MARK: - HTTP Request/Response Models

struct HTTPRequest {
    let head: HTTPRequestHead
    let body: Data?
}

struct HTTPResponse {
    let head: HTTPResponseHead
    let body: Data
}

struct HTTPRequestBuffer {
    private var head: HTTPRequestHead?
    private var body: Data = Data()
    
    mutating func processHead(_ head: HTTPRequestHead) {
        self.head = head
    }
    
    mutating func processBody(_ body: ByteBuffer) {
        self.body.append(contentsOf: body.readableBytesView)
    }
    
    func buildRequest() -> HTTPRequest {
        return HTTPRequest(head: head!, body: body.isEmpty ? nil : body)
    }
}

// MARK: - Server Errors

enum ServerError: Error {
    case sslConfigurationMissing
    case invalidConfiguration
}

// MARK: - Main Entry Point

func main() {
    let arguments = CommandLine.arguments
    
    // Parse command line arguments
    var config = ServerConfig()
    
    for i in 0..<arguments.count {
        switch arguments[i] {
        case "--host":
            if i + 1 < arguments.count {
                config = ServerConfig(host: arguments[i + 1])
            }
        case "--port":
            if i + 1 < arguments.count, let port = Int(arguments[i + 1]) {
                config = ServerConfig(port: port)
            }
        case "--data-dir":
            if i + 1 < arguments.count {
                config = ServerConfig(dataDirectory: arguments[i + 1])
            }
        case "--ssl":
            config = ServerConfig(sslEnabled: true)
        case "--help":
            print("ColibrìDB Server")
            print("Usage: coldb-server [options]")
            print("Options:")
            print("  --host HOST        Server host (default: 0.0.0.0)")
            print("  --port PORT        Server port (default: 5432)")
            print("  --data-dir DIR     Database directory (default: ./data)")
            print("  --ssl              Enable SSL/TLS")
            print("  --help             Show this help")
            exit(0)
        default:
            break
        }
    }
    
    do {
        let server = try DatabaseServer(config: config)
        
        // Handle shutdown signals
        let signalSource = DispatchSource.makeSignalSource(signal: SIGINT, queue: .main)
        signalSource.setEventHandler {
            print("\n🛑 Received SIGINT, shutting down...")
            try? server.stop()
            exit(0)
        }
        signalSource.resume()
        signal(SIGINT, SIG_IGN)
        
        try server.start()
    } catch {
        print("❌ Server failed to start: \(error)")
        exit(1)
    }
}

main()
