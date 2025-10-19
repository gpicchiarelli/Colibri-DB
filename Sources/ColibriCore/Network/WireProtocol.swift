//
//  WireProtocol.swift
//  Based on: spec/WireProtocol.tla
//

import Foundation

public enum MessageType: UInt8 {
    case auth = 0x01
    case authResponse = 0x02
    case query = 0x10
    case queryResponse = 0x11
    case prepare = 0x20
    case execute = 0x21
    case bind = 0x22
    case close = 0x30
    case error = 0xFF
}

public struct WireMessage {
    public let type: MessageType
    public let payload: Data
    
    public init(type: MessageType, payload: Data) {
        self.type = type
        self.payload = payload
    }
    
    public func serialize() -> Data {
        var data = Data()
        data.append(type.rawValue)
        
        var length = UInt32(payload.count)
        withUnsafeBytes(of: &length) { bytes in
            data.append(contentsOf: bytes)
        }
        
        data.append(payload)
        return data
    }
    
    public static func deserialize(_ data: Data) throws -> WireMessage {
        guard data.count >= 5 else {
            throw DBError.invalidData
        }
        
        let typeRaw = data[0]
        guard let type = MessageType(rawValue: typeRaw) else {
            throw DBError.invalidData
        }
        
        let lengthData = data[1..<5]
        let length = lengthData.withUnsafeBytes { $0.load(as: UInt32.self) }
        
        guard data.count >= 5 + Int(length) else {
            throw DBError.invalidData
        }
        
        let payload = data[5..<(5 + Int(length))]
        
        return WireMessage(type: type, payload: Data(payload))
    }
}

public actor WireProtocolHandler {
    public init() {}
    
    public func handleMessage(_ message: WireMessage) async throws -> WireMessage {
        switch message.type {
        case .auth:
            return try await handleAuth(message.payload)
        case .query:
            return try await handleQuery(message.payload)
        case .prepare:
            return try await handlePrepare(message.payload)
        case .execute:
            return try await handleExecute(message.payload)
        case .close:
            return WireMessage(type: .queryResponse, payload: Data())
        default:
            throw DBError.internalError("Unknown message type")
        }
    }
    
    private func handleAuth(_ payload: Data) async throws -> WireMessage {
        return WireMessage(type: .authResponse, payload: Data())
    }
    
    private func handleQuery(_ payload: Data) async throws -> WireMessage {
        return WireMessage(type: .queryResponse, payload: Data())
    }
    
    private func handlePrepare(_ payload: Data) async throws -> WireMessage {
        return WireMessage(type: .queryResponse, payload: Data())
    }
    
    private func handleExecute(_ payload: Data) async throws -> WireMessage {
        return WireMessage(type: .queryResponse, payload: Data())
    }
}

