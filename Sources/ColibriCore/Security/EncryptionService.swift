//
//  EncryptionService.swift
//  ColibrìDB Encryption Service
//
//  Implements: Data encryption/decryption
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import CryptoKit

// MARK: - Protocol Definition

/// Encryption service protocol (async to integrate with actors)
public protocol EncryptionService: Sendable {
    func encrypt(data: Data) async throws -> Data
    func decrypt(data: Data) async throws -> Data
}

// MARK: - Protocol Implementation

/// Default encryption service implementation
public actor DefaultEncryptionService: EncryptionService {
    // MARK: - Properties
    
    private let key: SymmetricKey
    
    // MARK: - Initialization
    
    /// Initialize encryption service
    /// - Parameter key: Optional symmetric key, or nil to generate a default one
    public init(key: SymmetricKey? = nil) {
        // Use provided key or generate a default one
        self.key = key ?? SymmetricKey(size: .bits256)
    }
    
    // MARK: - Protocol Implementation
    
    /// Encrypt data
    /// - Parameter data: Data to encrypt
    /// - Returns: Encrypted data
    public func encrypt(data: Data) async throws -> Data {
        let sealedBox = try AES.GCM.seal(data, using: key)
        guard let encrypted = sealedBox.combined else {
            throw EncryptionError.encryptionFailed
        }
        return encrypted
    }
    
    /// Decrypt data
    /// - Parameter data: Encrypted data to decrypt
    /// - Returns: Decrypted data
    public func decrypt(data: Data) async throws -> Data {
        let sealedBox = try AES.GCM.SealedBox(combined: data)
        return try AES.GCM.open(sealedBox, using: key)
    }
}

// MARK: - Error Types

/// Encryption-related errors
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

