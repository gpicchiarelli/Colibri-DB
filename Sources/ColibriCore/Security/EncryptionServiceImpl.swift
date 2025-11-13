//
//  EncryptionServiceImpl.swift
//  ColibrìDB Encryption Service Implementation
//
//  Concrete implementation of EncryptionService protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import CryptoKit

/// Concrete implementation of EncryptionService protocol
public actor EncryptionServiceImpl: EncryptionService {
    private let key: SymmetricKey
    
    public init(key: SymmetricKey? = nil) {
        // Use provided key or generate a default one
        self.key = key ?? SymmetricKey(size: .bits256)
    }
    
    public func encrypt(data: Data) async throws -> Data {
        let sealedBox = try AES.GCM.seal(data, using: key)
        guard let encrypted = sealedBox.combined else {
            throw EncryptionError.encryptionFailed
        }
        return encrypted
    }
    
    public func decrypt(data: Data) async throws -> Data {
        let sealedBox = try AES.GCM.SealedBox(combined: data)
        return try AES.GCM.open(sealedBox, using: key)
    }
}

public enum EncryptionError: Error, LocalizedError {
    case encryptionFailed
    case decryptionFailed
    
    public var errorDescription: String? {
        switch self {
        case .encryptionFailed:
            return "Encryption failed"
        case .decryptionFailed:
            return "Decryption failed"
        }
    }
}

