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
        logInfo("🚀 Starting ColibrìDB Server...")
        logInfo("📊 Database: \(config.dataDirectory)")
        logInfo("🌐 Server: \(config.host):\(config.port)")
        logInfo("🔒 SSL: \(config.sslEnabled ? "Enabled" : "Disabled")")
        logInfo("🔗 Max Connections: \(config.maxConnections)")
        logInfo("📝 Log Level: \(config.logLevel.rawValue)")
        
        let bootstrap = ServerBootstrap(group: group)
            .serverChannelOption(ChannelOptions.backlog, value: 256)
            .serverChannelOption(ChannelOptions.socket(SocketOptionLevel(SOL_SOCKET), SO_REUSEADDR), value: 1)
            .childChannelInitializer { channel in
                if self.config.sslEnabled {
                    return self.configureSSL(channel: channel)
                } else {
                    return self.configureProtocol(channel: channel)
                }
            }
            .childChannelOption(ChannelOptions.socket(IPPROTO_TCP, TCP_NODELAY), value: 1)
            .childChannelOption(ChannelOptions.socket(SocketOptionLevel(SOL_SOCKET), SO_REUSEADDR), value: 1)
            .childChannelOption(ChannelOptions.maxMessagesPerRead, value: 16)
            .childChannelOption(ChannelOptions.recvAllocator, value: AdaptiveRecvByteBufferAllocator())
        
        do {
            let channel = try bootstrap.bind(host: config.host, port: config.port).wait()
            self.serverChannel = channel
            
            logInfo("✅ Server started successfully on \(config.host):\(config.port)")
            
            // Start cleanup timer
            startCleanupTimer()
            
            // Wait for server to close
            try channel.closeFuture.wait()
        } catch {
            logError("❌ Failed to start server: \(error)")
            throw error
        }
    }
    
    func stop() throws {
        logInfo("🛑 Stopping ColibrìDB Server...")
        
        connectionManager.closeAllConnections()
        
        if let channel = serverChannel {
            try channel.close().wait()
        }
        
        try group.syncShutdownGracefully()
        logInfo("✅ Server stopped successfully")
    }
    
    private func startCleanupTimer() {
        Timer.scheduledTimer(withTimeInterval: 30.0, repeats: true) { _ in
            self.connectionManager.cleanupInactiveConnections()
        }
    }
    
    private func configureSSL(channel: Channel) -> EventLoopFuture<Void> {
        guard let certPath = config.sslCertificatePath,
              let keyPath = config.sslPrivateKeyPath else {
            return channel.eventLoop.makeFailedFuture(ConfigurationError.sslConfigurationIncomplete)
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
                self.configureProtocol(channel: channel)
            }
        } catch {
            return channel.eventLoop.makeFailedFuture(error)
        }
    }
    
    private func configureProtocol(channel: Channel) -> EventLoopFuture<Void> {
        let connectionID = connectionManager.createConnection(channel: channel)
        let protocolHandler = WireProtocolHandler(connectionManager: connectionManager, connectionID: connectionID)
        
        return channel.pipeline.addHandler(protocolHandler)
    }
}


// MARK: - Main Entry Point

func main() {
    let arguments = CommandLine.arguments
    
    // Parse command line arguments
    let config = ConfigurationParser.parse(from: arguments)
    
    // Validate configuration
    do {
        try ConfigurationValidator.validate(config)
    } catch {
        print("❌ Configuration error: \(error.localizedDescription)")
        exit(1)
    }
    
    do {
        let server = try DatabaseServer(config: config)
        
        // Handle shutdown signals
        let signalSource = DispatchSource.makeSignalSource(signal: SIGINT, queue: .main)
        signalSource.setEventHandler {
            logInfo("\n🛑 Received SIGINT, shutting down...")
            try? server.stop()
            exit(0)
        }
        signalSource.resume()
        signal(SIGINT, SIG_IGN)
        
        try server.start()
    } catch {
        logError("❌ Server failed to start: \(error)")
        exit(1)
    }
}

main()
