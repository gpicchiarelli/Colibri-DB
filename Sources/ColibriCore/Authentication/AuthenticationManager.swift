//
//  Authentication.swift
//  ColibrìDB Authentication Implementation
//
//  Based on: spec/Authentication.tla
//  Implements: User authentication and authorization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Security: Strong password hashing and validation
//  - Scalability: Efficient user management
//  - Reliability: Robust session management
//  - Compliance: Industry-standard security practices
//

import Foundation
import CryptoKit

// MARK: - User Types

/// User roles
/// Corresponds to TLA+: UserRole
public enum UserRole: String, Codable, Sendable {
    case admin = "admin"
    case user = "user"
    case readonly = "readonly"
    case guest = "guest"
}

/// User status
/// Corresponds to TLA+: UserStatus
public enum UserStatus: String, Codable, Sendable {
    case active = "active"
    case inactive = "inactive"
    case locked = "locked"
    case expired = "expired"
}

// MARK: - User Metadata

/// User metadata
/// Corresponds to TLA+: UserMetadata
public struct UserMetadata: Codable, Sendable, Equatable {
    public let username: String
    public let email: String
    public let role: UserRole
    public let status: UserStatus
    public let createdAt: Date
    public let lastLogin: Date?
    public let passwordHash: String
    public let salt: String
    
    public init(username: String, email: String, role: UserRole, status: UserStatus = .active, createdAt: Date = Date(), lastLogin: Date? = nil, passwordHash: String, salt: String) {
        self.username = username
        self.email = email
        self.role = role
        self.status = status
        self.createdAt = createdAt
        self.lastLogin = lastLogin
        self.passwordHash = passwordHash
        self.salt = salt
    }
}

// MARK: - Session Management

/// User session
/// Corresponds to TLA+: Session
public struct Session: Codable, Sendable, Equatable {
    public let sessionId: String
    public let username: String
    public let role: UserRole
    public let createdAt: Date
    public let expiresAt: Date
    public let isActive: Bool
    
    public init(sessionId: String, username: String, role: UserRole, createdAt: Date = Date(), expiresAt: Date, isActive: Bool = true) {
        self.sessionId = sessionId
        self.username = username
        self.role = role
        self.createdAt = createdAt
        self.expiresAt = expiresAt
        self.isActive = isActive
    }
}

// MARK: - Authentication Manager

/// Authentication Manager for user authentication and authorization
/// Corresponds to TLA+ module: Authentication.tla
public actor AuthenticationManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// User registry
    /// TLA+: users \in [Username -> UserMetadata]
    private var users: [String: UserMetadata] = [:]
    
    /// Active sessions
    /// TLA+: sessions \in [SessionId -> Session]
    private var sessions: [String: Session] = [:]
    
    /// Failed login attempts
    /// TLA+: failedAttempts \in [Username -> Nat]
    private var failedAttempts: [String: Int] = [:]
    
    /// Session timeout (in seconds)
    private let sessionTimeout: Int = 3600 // 1 hour
    
    /// Maximum failed attempts before lockout
    private let maxFailedAttempts: Int = 5
    
    /// Lockout duration (in seconds)
    private let lockoutDuration: Int = 1800 // 30 minutes
    
    /// User lockout timestamps
    private var lockoutTimestamps: [String: Date] = [:]
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init
        self.users = [:]
        self.sessions = [:]
        self.failedAttempts = [:]
        self.lockoutTimestamps = [:]
        
        // Create default admin user
        try? createUser(username: "admin", email: "admin@colibridb.com", password: "admin123", role: .admin)
    }
    
    // MARK: - User Management
    
    /// Create a new user
    /// TLA+ Action: CreateUser(username, email, password, role)
    public func createUser(username: String, email: String, password: String, role: UserRole) throws {
        // TLA+: Check if user already exists
        guard users[username] == nil else {
            throw AuthenticationError.userAlreadyExists
        }
        
        // TLA+: Validate password strength
        try validatePassword(password)
        
        // TLA+: Generate salt and hash password
        let salt = generateSalt()
        let passwordHash = hashPassword(password, salt: salt)
        
        // TLA+: Create user metadata
        let userMetadata = UserMetadata(
            username: username,
            email: email,
            role: role,
            passwordHash: passwordHash,
            salt: salt
        )
        
        users[username] = userMetadata
    }
    
    /// Update user role
    /// TLA+ Action: UpdateUserRole(username, newRole)
    public func updateUserRole(username: String, newRole: UserRole) throws {
        // TLA+: Check if user exists
        guard var user = users[username] else {
            throw AuthenticationError.userNotFound
        }
        
        // TLA+: Update user role
        let updatedUser = UserMetadata(
            username: user.username,
            email: user.email,
            role: newRole,
            status: user.status,
            createdAt: user.createdAt,
            lastLogin: user.lastLogin,
            passwordHash: user.passwordHash,
            salt: user.salt
        )
        
        users[username] = updatedUser
    }
    
    /// Delete user
    /// TLA+ Action: DeleteUser(username)
    public func deleteUser(username: String) throws {
        // TLA+: Check if user exists
        guard users[username] != nil else {
            throw AuthenticationError.userNotFound
        }
        
        // TLA+: Remove user and related data
        users.removeValue(forKey: username)
        failedAttempts.removeValue(forKey: username)
        lockoutTimestamps.removeValue(forKey: username)
        
        // Remove user's sessions
        sessions = sessions.filter { $0.value.username != username }
    }
    
    // MARK: - Authentication
    
    /// Authenticate user
    /// TLA+ Action: AuthenticateUser(username, password)
    public func authenticateUser(username: String, password: String) async throws -> Session {
        // TLA+: Check if user exists
        guard let user = users[username] else {
            throw AuthenticationError.invalidCredentials
        }
        
        // TLA+: Check if user is locked out
        if let lockoutTime = lockoutTimestamps[username] {
            let lockoutEnd = lockoutTime.addingTimeInterval(TimeInterval(lockoutDuration))
            if Date() < lockoutEnd {
                throw AuthenticationError.userLockedOut
            } else {
                // Lockout expired, reset
                lockoutTimestamps.removeValue(forKey: username)
                failedAttempts[username] = 0
            }
        }
        
        // TLA+: Check if user is active
        guard user.status == .active else {
            throw AuthenticationError.userInactive
        }
        
        // TLA+: Verify password
        let providedHash = hashPassword(password, salt: user.salt)
        guard providedHash == user.passwordHash else {
            // Increment failed attempts
            failedAttempts[username, default: 0] += 1
            
            // Check if user should be locked out
            if failedAttempts[username]! >= maxFailedAttempts {
                lockoutTimestamps[username] = Date()
                throw AuthenticationError.userLockedOut
            }
            
            throw AuthenticationError.invalidCredentials
        }
        
        // TLA+: Reset failed attempts on successful login
        failedAttempts[username] = 0
        
        // TLA+: Update last login time
        let updatedUser = UserMetadata(
            username: user.username,
            email: user.email,
            role: user.role,
            status: user.status,
            createdAt: user.createdAt,
            lastLogin: Date(),
            passwordHash: user.passwordHash,
            salt: user.salt
        )
        users[username] = updatedUser
        
        // TLA+: Create session
        let sessionId = generateSessionId()
        let expiresAt = Date().addingTimeInterval(TimeInterval(sessionTimeout))
        
        let session = Session(
            sessionId: sessionId,
            username: username,
            role: user.role,
            expiresAt: expiresAt
        )
        
        sessions[sessionId] = session
        
        return session
    }
    
    /// Validate session
    /// TLA+ Action: ValidateSession(sessionId)
    public func validateSession(sessionId: String) throws -> Session {
        // TLA+: Check if session exists
        guard let session = sessions[sessionId] else {
            throw AuthenticationError.invalidSession
        }
        
        // TLA+: Check if session is active
        guard session.isActive else {
            throw AuthenticationError.sessionInactive
        }
        
        // TLA+: Check if session has expired
        guard Date() < session.expiresAt else {
            // Remove expired session
            sessions.removeValue(forKey: sessionId)
            throw AuthenticationError.sessionExpired
        }
        
        return session
    }
    
    /// Logout user
    /// TLA+ Action: LogoutUser(sessionId)
    public func logoutUser(sessionId: String) throws {
        // TLA+: Check if session exists
        guard sessions[sessionId] != nil else {
            throw AuthenticationError.invalidSession
        }
        
        // TLA+: Remove session
        sessions.removeValue(forKey: sessionId)
    }
    
    /// Extend session
    /// TLA+ Action: ExtendSession(sessionId)
    public func extendSession(sessionId: String) throws {
        // TLA+: Check if session exists
        guard var session = sessions[sessionId] else {
            throw AuthenticationError.invalidSession
        }
        
        // TLA+: Extend session expiration
        let newExpiresAt = Date().addingTimeInterval(TimeInterval(sessionTimeout))
        let extendedSession = Session(
            sessionId: session.sessionId,
            username: session.username,
            role: session.role,
            createdAt: session.createdAt,
            expiresAt: newExpiresAt,
            isActive: session.isActive
        )
        
        sessions[sessionId] = extendedSession
    }
    
    // MARK: - Authorization
    
    /// Check if user has permission
    /// TLA+ Action: CheckPermission(username, resource, action)
    public func checkPermission(username: String, resource: String, action: String) throws -> Bool {
        // TLA+: Check if user exists
        guard let user = users[username] else {
            throw AuthenticationError.userNotFound
        }
        
        // TLA+: Check permissions based on role
        switch user.role {
        case .admin:
            return true // Admin has all permissions
        case .user:
            return action != "admin" // Users can do everything except admin actions
        case .readonly:
            return action == "read" // Readonly users can only read
        case .guest:
            return action == "read" && resource == "public" // Guests can only read public data
        }
    }
    
    // MARK: - Helper Methods
    
    /// Generate random salt
    private func generateSalt() -> String {
        let salt = Data((0..<32).map { _ in UInt8.random(in: 0...255) })
        return salt.base64EncodedString()
    }
    
    /// Hash password with salt
    private func hashPassword(_ password: String, salt: String) -> String {
        let passwordData = password.data(using: .utf8)!
        let saltData = Data(base64Encoded: salt)!
        let combined = passwordData + saltData
        
        let hash = SHA256.hash(data: combined)
        return Data(hash).base64EncodedString()
    }
    
    /// Generate session ID
    private func generateSessionId() -> String {
        let sessionData = Data((0..<32).map { _ in UInt8.random(in: 0...255) })
        return sessionData.base64EncodedString()
    }
    
    /// Validate password strength
    private func validatePassword(_ password: String) throws {
        guard password.count >= 8 else {
            throw AuthenticationError.weakPassword("Password must be at least 8 characters long")
        }
        
        guard password.rangeOfCharacter(from: .decimalDigits) != nil else {
            throw AuthenticationError.weakPassword("Password must contain at least one digit")
        }
        
        guard password.rangeOfCharacter(from: .letters) != nil else {
            throw AuthenticationError.weakPassword("Password must contain at least one letter")
        }
    }
    
    /// Clean up expired sessions
    public func cleanupExpiredSessions() {
        let now = Date()
        sessions = sessions.filter { $0.value.expiresAt > now }
    }
    
    // MARK: - Query Operations
    
    /// Get user by username
    public func getUser(username: String) -> UserMetadata? {
        return users[username]
    }
    
    /// Get all users
    public func getAllUsers() -> [UserMetadata] {
        return Array(users.values)
    }
    
    /// Get active sessions count
    public func getActiveSessionsCount() -> Int {
        return sessions.count
    }
    
    /// Get failed attempts for user
    public func getFailedAttempts(username: String) -> Int {
        return failedAttempts[username] ?? 0
    }
    
    /// Check if user is locked out
    public func isUserLockedOut(username: String) -> Bool {
        guard let lockoutTime = lockoutTimestamps[username] else {
            return false
        }
        
        let lockoutEnd = lockoutTime.addingTimeInterval(TimeInterval(lockoutDuration))
        return Date() < lockoutEnd
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check security invariant
    /// TLA+ Inv_Authentication_Security
    public func checkSecurityInvariant() -> Bool {
        // Check that all passwords are properly hashed
        for (_, user) in users {
            if user.passwordHash.isEmpty || user.salt.isEmpty {
                return false
            }
        }
        
        return true
    }
    
    /// Check scalability invariant
    /// TLA+ Inv_Authentication_Scalability
    public func checkScalabilityInvariant() -> Bool {
        // Check that session count is reasonable
        return sessions.count <= 10000 // Max 10k concurrent sessions
    }
    
    /// Check reliability invariant
    /// TLA+ Inv_Authentication_Reliability
    public func checkReliabilityInvariant() -> Bool {
        // Check that failed attempts are within limits
        for (_, attempts) in failedAttempts {
            if attempts > maxFailedAttempts {
                return false
            }
        }
        
        return true
    }
    
    /// Check compliance invariant
    /// TLA+ Inv_Authentication_Compliance
    public func checkComplianceInvariant() -> Bool {
        // Check that all sessions have proper expiration
        let now = Date()
        for (_, session) in sessions {
            if session.expiresAt <= now {
                return false
            }
        }
        
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let security = checkSecurityInvariant()
        let scalability = checkScalabilityInvariant()
        let reliability = checkReliabilityInvariant()
        let compliance = checkComplianceInvariant()
        
        return security && scalability && reliability && compliance
    }
}

// MARK: - Errors

public enum AuthenticationError: Error, LocalizedError {
    case userAlreadyExists
    case userNotFound
    case invalidCredentials
    case userInactive
    case userLockedOut
    case invalidSession
    case sessionInactive
    case sessionExpired
    case weakPassword(String)
    
    public var errorDescription: String? {
        switch self {
        case .userAlreadyExists:
            return "User already exists"
        case .userNotFound:
            return "User not found"
        case .invalidCredentials:
            return "Invalid credentials"
        case .userInactive:
            return "User account is inactive"
        case .userLockedOut:
            return "User account is locked out"
        case .invalidSession:
            return "Invalid session"
        case .sessionInactive:
            return "Session is inactive"
        case .sessionExpired:
            return "Session has expired"
        case .weakPassword(let message):
            return "Weak password: \(message)"
        }
    }
}
