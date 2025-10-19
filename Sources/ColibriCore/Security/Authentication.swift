//
//  Authentication.swift
//  ColibrìDB Authentication System
//
//  Based on: spec/Authentication.tla
//  Implements: User authentication with password hashing
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import Crypto

/// User credentials
public struct UserCredentials: Codable, Sendable {
    public let username: String
    public let passwordHash: String
    public let salt: String
    public let createdAt: Date
    
    public init(username: String, passwordHash: String, salt: String) {
        self.username = username
        self.passwordHash = passwordHash
        self.salt = salt
        self.createdAt = Date()
    }
}

/// Authentication Manager
/// Corresponds to TLA+ module: Authentication.tla
public actor AuthenticationManager {
    // MARK: - State
    
    private var users: [String: UserCredentials] = [:]
    private var sessions: [String: String] = [:]  // sessionToken -> username
    
    // MARK: - Initialization
    
    public init() {
        // Create default admin user
        try? createUser(username: "admin", password: "admin")
    }
    
    // MARK: - User Management
    
    /// Create a new user
    public func createUser(username: String, password: String) throws {
        guard users[username] == nil else {
            throw DBError.duplicate
        }
        
        // Generate salt
        let salt = generateSalt()
        
        // Hash password
        let passwordHash = hashPassword(password, salt: salt)
        
        // Create user
        let credentials = UserCredentials(username: username, passwordHash: passwordHash, salt: salt)
        users[username] = credentials
    }
    
    /// Authenticate user
    public func authenticate(username: String, password: String) throws -> String {
        guard let credentials = users[username] else {
            throw DBError.notFound
        }
        
        // Verify password
        let passwordHash = hashPassword(password, salt: credentials.salt)
        
        guard passwordHash == credentials.passwordHash else {
            throw DBError.internalError("Invalid password")
        }
        
        // Create session
        let sessionToken = generateSessionToken()
        sessions[sessionToken] = username
        
        return sessionToken
    }
    
    /// Validate session
    public func validateSession(_ token: String) -> String? {
        return sessions[token]
    }
    
    /// Logout
    public func logout(token: String) {
        sessions[token] = nil
    }
    
    // MARK: - Private Helpers
    
    private func generateSalt() -> String {
        return UUID().uuidString
    }
    
    private func generateSessionToken() -> String {
        return UUID().uuidString
    }
    
    private func hashPassword(_ password: String, salt: String) -> String {
        let combined = password + salt
        let data = Data(combined.utf8)
        let hash = SHA256.hash(data: data)
        return hash.compactMap { String(format: "%02x", $0) }.joined()
    }
}

