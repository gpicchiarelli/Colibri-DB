//
//  WireProtocol.swift
//  coldb-server
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Wire protocol for client-server communication

import Foundation
import NIO
import ColibriCore

// MARK: - Wire Protocol

public enum WireProtocol {
    case postgres
    case mysql
    case http
    case custom
}

// MARK: - Message Types

public enum MessageType: UInt8, Sendable {
    case query = 0x51        // 'Q'
    case queryResult = 0x52  // 'R'
    case error = 0x45        // 'E'
    case ready = 0x5A        // 'Z'
    case terminate = 0x58    // 'X'
    case begin = 0x42        // 'B'
    case commit = 0x43       // 'C'
    case rollback = 0x54     // 'T'
}

// MARK: - Wire Message

public struct WireMessage {
    public let type: MessageType
    public let length: Int32
    public let payload: Data
    
    public init(type: MessageType, payload: Data) {
        self.type = type
        self.payload = payload
        self.length = Int32(payload.count + 4) // +4 for length field
    }
}

// MARK: - Message Serialization

public struct MessageSerializer {
    public static func serialize(_ message: WireMessage) -> Data {
        var data = Data()
        
        // Message type
        data.append(message.type.rawValue)
        
        // Length (including length field itself)
        var length = message.length.bigEndian
        data.append(Data(bytes: &length, count: 4))
        
        // Payload
        data.append(message.payload)
        
        return data
    }
    
    public static func deserialize(from data: Data) throws -> WireMessage {
        guard data.count >= 5 else {
            throw WireProtocolError.invalidMessage("Message too short")
        }
        
        let typeByte = data[0]
        guard let type = MessageType(rawValue: typeByte) else {
            throw WireProtocolError.invalidMessage("Unknown message type: \(typeByte)")
        }
        
        let lengthData = data.subdata(in: 1..<5)
        let length = lengthData.withUnsafeBytes { $0.load(as: Int32.self).bigEndian }
        
        guard data.count >= Int(length) + 1 else {
            throw WireProtocolError.invalidMessage("Incomplete message")
        }
        
        let payload = data.subdata(in: 5..<Int(length) + 1)
        
        return WireMessage(type: type, payload: payload)
    }
}

// MARK: - Query Message

public struct QueryMessage {
    public let sql: String
    
    public init(sql: String) {
        self.sql = sql
    }
    
    public func serialize() -> Data {
        return sql.data(using: .utf8) ?? Data()
    }
    
    public static func deserialize(from data: Data) throws -> QueryMessage {
        guard let sql = String(data: data, encoding: .utf8) else {
            throw WireProtocolError.invalidMessage("Invalid UTF-8 in query")
        }
        return QueryMessage(sql: sql)
    }
}

// MARK: - Query Result Message

public struct QueryResultMessage {
    public let result: SQLQueryResult
    
    public init(result: SQLQueryResult) {
        self.result = result
    }
    
    public func serialize() -> Data {
        do {
            let encoder = JSONEncoder()
            encoder.outputFormatting = .sortedKeys
            return try encoder.encode(result)
        } catch {
            return Data("{\"error\":\"Failed to serialize result\"}".utf8)
        }
    }
    
    public static func deserialize(from data: Data) throws -> QueryResultMessage {
        do {
            let decoder = JSONDecoder()
            let result = try decoder.decode(SQLQueryResult.self, from: data)
            return QueryResultMessage(result: result)
        } catch {
            throw WireProtocolError.invalidMessage("Failed to deserialize query result")
        }
    }
}

// MARK: - Error Message

public struct ErrorMessage {
    public let code: String
    public let message: String
    public let severity: String
    
    public init(code: String, message: String, severity: String = "ERROR") {
        self.code = code
        self.message = message
        self.severity = severity
    }
    
    public func serialize() -> Data {
        let errorData = [
            "code": code,
            "message": message,
            "severity": severity
        ]
        
        do {
            let encoder = JSONEncoder()
            return try encoder.encode(errorData)
        } catch {
            return Data("{\"error\":\"Failed to serialize error\"}".utf8)
        }
    }
    
    public static func deserialize(from data: Data) throws -> ErrorMessage {
        do {
            let decoder = JSONDecoder()
            let errorData = try decoder.decode([String: String].self, from: data)
            
            guard let code = errorData["code"],
                  let message = errorData["message"] else {
                throw WireProtocolError.invalidMessage("Missing required error fields")
            }
            
            return ErrorMessage(
                code: code,
                message: message,
                severity: errorData["severity"] ?? "ERROR"
            )
        } catch {
            throw WireProtocolError.invalidMessage("Failed to deserialize error message")
        }
    }
}

// MARK: - Ready Message

public struct ReadyMessage {
    public let status: String
    
    public init(status: String = "READY") {
        self.status = status
    }
    
    public func serialize() -> Data {
        return status.data(using: .utf8) ?? Data()
    }
    
    public static func deserialize(from data: Data) throws -> ReadyMessage {
        guard let status = String(data: data, encoding: .utf8) else {
            throw WireProtocolError.invalidMessage("Invalid UTF-8 in ready message")
        }
        return ReadyMessage(status: status)
    }
}

// MARK: - Wire Protocol Errors

public enum WireProtocolError: Error, LocalizedError {
    case invalidMessage(String)
    case unsupportedMessageType(MessageType)
    case serializationError(String)
    case deserializationError(String)
    
    public var errorDescription: String? {
        switch self {
        case .invalidMessage(let message):
            return "Invalid message: \(message)"
        case .unsupportedMessageType(let type):
            return "Unsupported message type: \(type)"
        case .serializationError(let message):
            return "Serialization error: \(message)"
        case .deserializationError(let message):
            return "Deserialization error: \(message)"
        }
    }
}

// MARK: - Protocol Handler

public final class WireProtocolHandler: ChannelInboundHandler {
    public typealias InboundIn = ByteBuffer
    public typealias OutboundOut = ByteBuffer
    
    private let connectionManager: ConnectionManager
    private let connectionID: ConnectionID
    private var messageBuffer = Data()
    
    public init(connectionManager: ConnectionManager, connectionID: ConnectionID) {
        self.connectionManager = connectionManager
        self.connectionID = connectionID
    }
    
    public func channelRead(context: ChannelHandlerContext, data: NIOAny) {
        var buffer = unwrapInboundIn(data)
        let readableBytes = buffer.readableBytes
        
        guard let data = buffer.getData(at: buffer.readerIndex, length: readableBytes) else {
            logError("Failed to read data from buffer")
            return
        }
        
        messageBuffer.append(data)
        processMessages(context: context)
    }
    
    private func processMessages(context: ChannelHandlerContext) {
        while messageBuffer.count >= 5 {
            let typeByte = messageBuffer[0]
            let lengthData = messageBuffer.subdata(in: 1..<5)
            let length = lengthData.withUnsafeBytes { $0.load(as: Int32.self).bigEndian }
            
            let totalMessageLength = Int(length) + 1
            
            guard messageBuffer.count >= totalMessageLength else {
                // Incomplete message, wait for more data
                break
            }
            
            let messageData = messageBuffer.subdata(in: 0..<totalMessageLength)
            messageBuffer.removeFirst(totalMessageLength)
            
            do {
                let message = try MessageSerializer.deserialize(from: messageData)
                try handleMessage(context: context, message: message)
            } catch {
                logError("Failed to process message: \(error)")
                sendError(context: context, error: error)
            }
        }
    }
    
    private func handleMessage(context: ChannelHandlerContext, message: WireMessage) throws {
        guard let connection = connectionManager.getConnection(id: connectionID) else {
            throw WireProtocolError.invalidMessage("Connection not found")
        }
        
        switch message.type {
        case .query:
            let queryMessage = try QueryMessage.deserialize(from: message.payload)
            handleQuery(context: context, connection: connection, query: queryMessage)
            
        case .begin:
            handleBeginTransaction(context: context, connection: connection)
            
        case .commit:
            handleCommitTransaction(context: context, connection: connection)
            
        case .rollback:
            handleRollbackTransaction(context: context, connection: connection)
            
        case .terminate:
            handleTerminate(context: context, connection: connection)
            
        default:
            throw WireProtocolError.unsupportedMessageType(message.type)
        }
    }
    
    private func handleQuery(context: ChannelHandlerContext, connection: DatabaseConnection, query: QueryMessage) {
        connection.executeQuery(query.sql)
            .whenComplete { result in
                switch result {
                case .success(let queryResult):
                    self.sendQueryResult(context: context, result: queryResult)
                case .failure(let error):
                    self.sendError(context: context, error: error)
                }
            }
    }
    
    private func handleBeginTransaction(context: ChannelHandlerContext, connection: DatabaseConnection) {
        connection.beginTransaction()
            .whenComplete { result in
                switch result {
                case .success:
                    self.sendReady(context: context)
                case .failure(let error):
                    self.sendError(context: context, error: error)
                }
            }
    }
    
    private func handleCommitTransaction(context: ChannelHandlerContext, connection: DatabaseConnection) {
        connection.commitTransaction()
            .whenComplete { result in
                switch result {
                case .success:
                    self.sendReady(context: context)
                case .failure(let error):
                    self.sendError(context: context, error: error)
                }
            }
    }
    
    private func handleRollbackTransaction(context: ChannelHandlerContext, connection: DatabaseConnection) {
        connection.rollbackTransaction()
            .whenComplete { result in
                switch result {
                case .success:
                    self.sendReady(context: context)
                case .failure(let error):
                    self.sendError(context: context, error: error)
                }
            }
    }
    
    private func handleTerminate(context: ChannelHandlerContext, connection: DatabaseConnection) {
        connection.close()
        context.close(promise: nil)
    }
    
    private func sendQueryResult(context: ChannelHandlerContext, result: SQLQueryResult) {
        let resultMessage = QueryResultMessage(result: result)
        let wireMessage = WireMessage(type: .queryResult, payload: resultMessage.serialize())
        let data = MessageSerializer.serialize(wireMessage)
        
        var buffer = context.channel.allocator.buffer(capacity: data.count)
        buffer.writeBytes(data)
        context.writeAndFlush(wrapOutboundOut(buffer), promise: nil)
    }
    
    private func sendError(context: ChannelHandlerContext, error: Error) {
        let errorMessage = ErrorMessage(
            code: "INTERNAL_ERROR",
            message: error.localizedDescription
        )
        let wireMessage = WireMessage(type: .error, payload: errorMessage.serialize())
        let data = MessageSerializer.serialize(wireMessage)
        
        var buffer = context.channel.allocator.buffer(capacity: data.count)
        buffer.writeBytes(data)
        context.writeAndFlush(wrapOutboundOut(buffer), promise: nil)
    }
    
    private func sendReady(context: ChannelHandlerContext) {
        let readyMessage = ReadyMessage()
        let wireMessage = WireMessage(type: .ready, payload: readyMessage.serialize())
        let data = MessageSerializer.serialize(wireMessage)
        
        var buffer = context.channel.allocator.buffer(capacity: data.count)
        buffer.writeBytes(data)
        context.writeAndFlush(wrapOutboundOut(buffer), promise: nil)
    }
}
