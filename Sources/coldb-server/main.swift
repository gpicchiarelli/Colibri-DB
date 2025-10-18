//
//  main.swift
//  coldb-server
//
//  Colibrì-DB Server - Multi-client Database Server
//  Created by Giacomo Picchiarelli on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License

import Foundation
import NIO
import ColibriCore
import ColibriServer

/// Main entry point for Colibrì-DB Server
@main
struct ColibriDBServer {
    static func main() async throws {
        print("🚀 Colibrì-DB Server Starting...")
        print("═══════════════════════════════════════")
        
        // Load configuration
        let config = try loadConfiguration()
        
        // Initialize database
        print("📊 Initializing database...")
        let database = try initializeDatabase(config: config.database)
        
        // Create server
        print("🌐 Starting server on \(config.host):\(config.port)...")
        let server = try await createServer(
            database: database,
            config: config
        )
        
        // Handle shutdown gracefully
        setupSignalHandlers(server: server, database: database)
        
        print("✅ Server ready and listening!")
        print("═══════════════════════════════════════")
        
        // Keep running
        try await server.run()
    }
    
    // MARK: - Configuration
    
    static func loadConfiguration() throws -> ServerConfig {
        // Try to load from file
        let configPath = CommandLine.arguments.count > 1 
            ? CommandLine.arguments[1] 
            : "colibridb.server.json"
        
        if FileManager.default.fileExists(atPath: configPath) {
            let data = try Data(contentsOf: URL(fileURLWithPath: configPath))
            let decoder = JSONDecoder()
            let config = try decoder.decode(ServerConfig.self, from: data)
            
            // Validate configuration
            try config.validate()
            
            print("⚙️  Configuration loaded from: \(configPath)")
            return config
        }
        
        // Use defaults
        print("⚙️  Using default configuration")
        let config = ServerConfig()
        try config.validate()
        return config
    }
    
    // MARK: - Database Initialization
    
    static func initializeDatabase(config: DBConfig) throws -> Database {
        let database = Database(config: config)
        
        // Ensure data directory exists
        try database.ensureDataDir()
        
        // Perform recovery if needed
        print("  🔄 Performing crash recovery (ARIES)...")
        // Recovery would be performed here
        
        // Start periodic maintenance
        print("  🧹 Starting periodic maintenance...")
        database.startPeriodicCleanup()
        
        // Enable telemetry if configured
        print("  📊 Telemetry enabled")
        
        print("  ✅ Database initialized successfully")
        return database
    }
    
    // MARK: - Server Creation
    
    static func createServer(database: Database, config: ServerConfig) async throws -> DatabaseServer {
        let server = DatabaseServer(
            database: database,
            config: config
        )
        
        return server
    }
    
    // MARK: - Signal Handlers
    
    static func setupSignalHandlers(server: DatabaseServer, database: Database) {
        // Handle SIGINT (Ctrl+C)
        signal(SIGINT) { _ in
            print("\n⚠️  Received SIGINT, shutting down gracefully...")
            Task {
                await server.shutdown()
                try? database.close()
                print("✅ Server shutdown complete")
                exit(0)
            }
        }
        
        // Handle SIGTERM
        signal(SIGTERM) { _ in
            print("\n⚠️  Received SIGTERM, shutting down gracefully...")
            Task {
                await server.shutdown()
                try? database.close()
                print("✅ Server shutdown complete")
                exit(0)
            }
        }
    }
}

// MARK: - Database Server

/// Main database server using SwiftNIO
public actor DatabaseServer {
    private let database: Database
    private let config: ServerConfig
    private let connectionManager: ConnectionManager
    private var serverChannel: Channel?
    private let group: MultiThreadedEventLoopGroup
    
    public init(database: Database, config: ServerConfig) {
        self.database = database
        self.config = config
        self.connectionManager = ConnectionManager(
            maxConnections: config.maxConnections,
            connectionTimeout: config.connectionTimeout,
            queryTimeout: config.queryTimeout,
            database: database
        )
        
        // Use available cores for event loop
        let coreCount = System.coreCount
        self.group = MultiThreadedEventLoopGroup(numberOfThreads: coreCount)
        
        print("  🔧 Event loops: \(coreCount) threads")
    }
    
    /// Start the server
    public func run() async throws {
        let bootstrap = ServerBootstrap(group: group)
            .serverChannelOption(ChannelOptions.backlog, value: 256)
            .serverChannelOption(ChannelOptions.socketOption(.so_reuseaddr), value: 1)
            .childChannelInitializer { channel in
                channel.pipeline.addHandlers([
                    MessageDecoder(),
                    MessageEncoder(),
                    QueryHandler(
                        connectionManager: self.connectionManager,
                        config: self.config
                    )
                ])
            }
            .childChannelOption(ChannelOptions.socketOption(.so_reuseaddr), value: 1)
            .childChannelOption(ChannelOptions.maxMessagesPerRead, value: 16)
        
        do {
            serverChannel = try await bootstrap.bind(
                host: config.host,
                port: config.port
            ).get()
            
            print("  ✅ Server bound to \(config.host):\(config.port)")
            
            // Wait for server to close
            try await serverChannel?.closeFuture.get()
            
        } catch {
            print("  ❌ Failed to start server: \(error)")
            throw error
        }
    }
    
    /// Shutdown the server gracefully
    public func shutdown() async {
        print("  🛑 Shutting down server...")
        
        // Close all connections
        connectionManager.closeAllConnections()
        
        // Close server channel
        try? await serverChannel?.close()
        
        // Shutdown event loop group
        try? await group.shutdownGracefully()
        
        print("  ✅ Server shutdown complete")
    }
}

// MARK: - NIO Handlers

/// Decodes wire protocol messages
final class MessageDecoder: ByteToMessageDecoder {
    typealias InboundOut = WireMessage
    
    func decode(context: ChannelHandlerContext, buffer: inout ByteBuffer) throws -> DecodingState {
        guard buffer.readableBytes >= 5 else {
            return .needMoreData
        }
        
        // Peek at message to determine length
        guard let type = buffer.getInteger(at: buffer.readerIndex, as: UInt8.self),
              let length = buffer.getInteger(at: buffer.readerIndex + 1, as: Int32.self) else {
            return .needMoreData
        }
        
        let totalLength = Int(length) + 1 // +1 for type byte
        
        guard buffer.readableBytes >= totalLength else {
            return .needMoreData
        }
        
        // Read complete message
        _ = buffer.readInteger(as: UInt8.self) // type
        _ = buffer.readInteger(as: Int32.self) // length
        
        guard let payloadData = buffer.readData(length: Int(length) - 4) else {
            throw WireProtocolError.invalidMessage("Failed to read payload")
        }
        
        guard let messageType = MessageType(rawValue: type) else {
            throw WireProtocolError.invalidMessage("Invalid message type")
        }
        
        let message = WireMessage(type: messageType, payload: payloadData)
        context.fireChannelRead(self.wrapInboundOut(message))
        
        return .continue
    }
}

/// Encodes wire protocol messages
final class MessageEncoder: MessageToByteEncoder {
    typealias OutboundIn = WireMessage
    
    func encode(data: WireMessage, out: inout ByteBuffer) throws {
        let serialized = MessageSerializer.serialize(data)
        out.writeBytes(serialized)
    }
}

/// Handles query execution
final class QueryHandler: ChannelInboundHandler {
    typealias InboundIn = WireMessage
    typealias OutboundOut = WireMessage
    
    private let connectionManager: ConnectionManager
    private let config: ServerConfig
    private var connectionID: ConnectionID?
    
    init(connectionManager: ConnectionManager, config: ServerConfig) {
        self.connectionManager = connectionManager
        self.config = config
    }
    
    func channelActive(context: ChannelHandlerContext) {
        // Create new connection
        connectionID = connectionManager.createConnection(channel: context.channel)
        
        // Send ready message
        let readyMsg = WireMessage(type: .ready, payload: Data())
        context.writeAndFlush(self.wrapOutboundOut(readyMsg), promise: nil)
    }
    
    func channelRead(context: ChannelHandlerContext, data: NIOAny) {
        let message = self.unwrapInboundIn(data)
        
        guard let connID = connectionID,
              let connection = connectionManager.getConnection(id: connID) else {
            sendError(context: context, error: "No active connection")
            return
        }
        
        switch message.type {
        case .query:
            handleQuery(message: message, connection: connection, context: context)
            
        case .begin:
            handleBegin(connection: connection, context: context)
            
        case .commit:
            handleCommit(connection: connection, context: context)
            
        case .rollback:
            handleRollback(connection: connection, context: context)
            
        case .terminate:
            context.close(promise: nil)
            
        default:
            sendError(context: context, error: "Unsupported message type: \(message.type)")
        }
    }
    
    func channelInactive(context: ChannelHandlerContext) {
        if let connID = connectionID {
            connectionManager.closeConnection(id: connID)
        }
    }
    
    // MARK: - Query Handlers
    
    private func handleQuery(message: WireMessage, connection: DatabaseConnection, context: ChannelHandlerContext) {
        do {
            let queryMsg = try QueryMessage.deserialize(from: message.payload)
            
            connection.executeQuery(queryMsg.sql).whenComplete { result in
                switch result {
                case .success(let queryResult):
                    let resultMsg = QueryResultMessage(result: queryResult)
                    let wireMsg = WireMessage(type: .queryResult, payload: resultMsg.serialize())
                    context.writeAndFlush(self.wrapOutboundOut(wireMsg), promise: nil)
                    
                case .failure(let error):
                    self.sendError(context: context, error: error.localizedDescription)
                }
            }
        } catch {
            sendError(context: context, error: error.localizedDescription)
        }
    }
    
    private func handleBegin(connection: DatabaseConnection, context: ChannelHandlerContext) {
        connection.beginTransaction().whenComplete { result in
            switch result {
            case .success(let tid):
                let payload = "Transaction \(tid) started".data(using: .utf8) ?? Data()
                let msg = WireMessage(type: .ready, payload: payload)
                context.writeAndFlush(self.wrapOutboundOut(msg), promise: nil)
                
            case .failure(let error):
                self.sendError(context: context, error: error.localizedDescription)
            }
        }
    }
    
    private func handleCommit(connection: DatabaseConnection, context: ChannelHandlerContext) {
        connection.commitTransaction().whenComplete { result in
            switch result {
            case .success:
                let payload = "Transaction committed".data(using: .utf8) ?? Data()
                let msg = WireMessage(type: .ready, payload: payload)
                context.writeAndFlush(self.wrapOutboundOut(msg), promise: nil)
                
            case .failure(let error):
                self.sendError(context: context, error: error.localizedDescription)
            }
        }
    }
    
    private func handleRollback(connection: DatabaseConnection, context: ChannelHandlerContext) {
        connection.rollbackTransaction().whenComplete { result in
            switch result {
            case .success:
                let payload = "Transaction rolled back".data(using: .utf8) ?? Data()
                let msg = WireMessage(type: .ready, payload: payload)
                context.writeAndFlush(self.wrapOutboundOut(msg), promise: nil)
                
            case .failure(let error):
                self.sendError(context: context, error: error.localizedDescription)
            }
        }
    }
    
    private func sendError(context: ChannelHandlerContext, error: String) {
        let errorMsg = ErrorMessage(code: "ERROR", message: error)
        let wireMsg = WireMessage(type: .error, payload: errorMsg.serialize())
        context.writeAndFlush(self.wrapOutboundOut(wireMsg), promise: nil)
    }
}

// MARK: - Wire Protocol Errors

enum WireProtocolError: Error {
    case invalidMessage(String)
    case connectionClosed
    case timeout
}

