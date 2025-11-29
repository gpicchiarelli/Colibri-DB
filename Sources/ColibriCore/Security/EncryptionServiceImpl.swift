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
    // MARK: - Properties
    
    private let key: SymmetricKey
    
    // MARK: - Initialization
    
    /// Initialize encryption service implementation
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

