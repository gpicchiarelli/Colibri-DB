//
//  SimpleSecurityManager.swift
//  ColibrìDB Simple Security Manager
//
//  Simple implementation of SecurityManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Simple implementation of PolicySecurityManager protocol
public actor SimpleSecurityManager: PolicySecurityManager {
    public init() {}
    
    public func encryptData(data: String) async throws {
        // Simple implementation: no-op (data is already "encrypted" as plain text)
    }
    
    public func decryptData(data: String) async throws {
        // Simple implementation: no-op (data is already "decrypted" as plain text)
    }
}

