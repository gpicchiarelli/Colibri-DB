//
//  SQLUserStore.swift
//  ColibrìDB
//
//  Created by ColibrìDB Team on 2025-10-19.
//
//  SQL-backed persistence for users and sessions
//

import Foundation

/// Protocol for user and session storage
/// Provides persistence for authentication data
public protocol UserStore: Sendable {
    func initializeSchema() async throws
    // Users
    func createUser(_ user: UserMetadata) async throws
    func getUser(username: String) async throws -> UserMetadata?
    func getAllUsers() async throws -> [UserMetadata]
    func updateUserRole(username: String, newRole: UserRole) async throws
    func updatePassword(username: String, passwordHash: String, salt: String) async throws
    func updateLastLogin(username: String, at: Date) async throws
    func deleteUser(username: String) async throws
    // Sessions
    func createSession(_ session: Session) async throws
    func getSession(sessionId: String) async throws -> Session?
    func deleteSession(sessionId: String) async throws
    func cleanupExpiredSessions(now: Date) async throws
}

/// SQL-backed implementation of UserStore
/// Stores user and session data in database tables
public actor SQLUserStore: UserStore {
    // MARK: - Properties
    
    private let db: ColibrìDB
    private let schema: String = "colibri_sys"
    
    // MARK: - Initialization
    
    /// Initialize SQL user store
    /// - Parameter database: Database instance for storage
    public init(database: ColibrìDB) {
        self.db = database
    }
    
    // MARK: - Schema Management
    
    /// Initialize database schema for users and sessions
    /// Creates necessary tables if they don't exist
    public func initializeSchema() async throws {
        // Create private schema for server
        _ = try await db.executeQuery("CREATE SCHEMA IF NOT EXISTS \(schema);", txId: try await db.beginTransaction())
        
        // Users table
        _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).users (
                username TEXT PRIMARY KEY,
                email TEXT NOT NULL,
                role TEXT NOT NULL,
                status TEXT NOT NULL,
                created_at DOUBLE NOT NULL,
                last_login DOUBLE NULL,
                password_hash TEXT NOT NULL,
                salt TEXT NOT NULL
            );
        """, txId: try await db.beginTransaction())
        // Sessions table
        _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sessions (
                session_id TEXT PRIMARY KEY,
                username TEXT NOT NULL,
                role TEXT NOT NULL,
                created_at DOUBLE NOT NULL,
                expires_at DOUBLE NOT NULL,
                is_active INTEGER NOT NULL
            );
        """, txId: try await db.beginTransaction())
        // Server settings table
        _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).server_settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
        """, txId: try await db.beginTransaction())
    }
    
    // MARK: - User Management
    
    /// Create a new user
    /// - Parameter user: User metadata to create
    public func createUser(_ user: UserMetadata) async throws {
        let ts = user.createdAt.timeIntervalSince1970
        let ll = user.lastLogin?.timeIntervalSince1970
        let lastLoginString = ll != nil ? "\(ll!)" : "NULL"
        let sql = """
            INSERT INTO \(schema).users (username, email, role, status, created_at, last_login, password_hash, salt)
            VALUES ('\(escape(user.username))','\(escape(user.email))','\(user.role.rawValue)','\(user.status.rawValue)',\(ts),\(lastLoginString),'\(escape(user.passwordHash))','\(escape(user.salt))');
        """
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Get user by username
    /// - Parameter username: Username to lookup
    /// - Returns: User metadata if found, nil otherwise
    public func getUser(username: String) async throws -> UserMetadata? {
        let sql = "SELECT username,email,role,status,created_at,last_login,password_hash,salt FROM \(schema).users WHERE username = '\(escape(username))' LIMIT 1;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        guard let row = result.rows.first else { return nil }
        let role = UserRole(rawValue: str(row["role"]) ?? "user") ?? .user
        let status = UserStatus(rawValue: str(row["status"]) ?? "active") ?? .active
        let createdAt = Date(timeIntervalSince1970: dbl(row["created_at"]) ?? 0)
        let lastLogin: Date? = dbl(row["last_login"]).map { Date(timeIntervalSince1970: $0) }
        return UserMetadata(
            username: str(row["username"]) ?? username,
            email: str(row["email"]) ?? "",
            role: role,
            status: status,
            createdAt: createdAt,
            lastLogin: lastLogin,
            passwordHash: str(row["password_hash"]) ?? "",
            salt: str(row["salt"]) ?? ""
        )
    }
    
    /// Get all users
    /// - Returns: Array of all user metadata
    public func getAllUsers() async throws -> [UserMetadata] {
        let sql = "SELECT username,email,role,status,created_at,last_login,password_hash,salt FROM \(schema).users;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        return result.rows.map { row in
            let role = UserRole(rawValue: str(row["role"]) ?? "user") ?? .user
            let status = UserStatus(rawValue: str(row["status"]) ?? "active") ?? .active
            let createdAt = Date(timeIntervalSince1970: dbl(row["created_at"]) ?? 0)
            let lastLogin: Date? = dbl(row["last_login"]).map { Date(timeIntervalSince1970: $0) }
            return UserMetadata(
                username: str(row["username"]) ?? "",
                email: str(row["email"]) ?? "",
                role: role,
                status: status,
                createdAt: createdAt,
                lastLogin: lastLogin,
                passwordHash: str(row["password_hash"]) ?? "",
                salt: str(row["salt"]) ?? ""
            )
        }
    }
    
    /// Update user role
    /// - Parameters:
    ///   - username: Username to update
    ///   - newRole: New role to assign
    public func updateUserRole(username: String, newRole: UserRole) async throws {
        let sql = "UPDATE \(schema).users SET role = '\(newRole.rawValue)' WHERE username = '\(escape(username))';"
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Update user password
    /// - Parameters:
    ///   - username: Username to update
    ///   - passwordHash: New password hash
    ///   - salt: Password salt
    public func updatePassword(username: String, passwordHash: String, salt: String) async throws {
        let sql = "UPDATE \(schema).users SET password_hash = '\(escape(passwordHash))', salt = '\(escape(salt))' WHERE username = '\(escape(username))';"
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Update last login timestamp
    /// - Parameters:
    ///   - username: Username to update
    ///   - at: Login timestamp
    public func updateLastLogin(username: String, at: Date) async throws {
        let ts = at.timeIntervalSince1970
        let sql = "UPDATE \(schema).users SET last_login = \(ts) WHERE username = '\(escape(username))';"
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Delete user and associated sessions
    /// - Parameter username: Username to delete
    public func deleteUser(username: String) async throws {
        let sql1 = "DELETE FROM \(schema).sessions WHERE username = '\(escape(username))';"
        let sql2 = "DELETE FROM \(schema).users WHERE username = '\(escape(username))';"
        let tx = try await db.beginTransaction()
        _ = try await db.executeQuery(sql1, txId: tx)
        _ = try await db.executeQuery(sql2, txId: tx)
        try await db.commit(txId: tx)
    }
    
    // MARK: - Session Management
    
    /// Create a new session
    /// - Parameter session: Session data to create
    public func createSession(_ session: Session) async throws {
        let sql = """
            INSERT INTO \(schema).sessions (session_id,username,role,created_at,expires_at,is_active)
            VALUES ('\(escape(session.sessionId))','\(escape(session.username))','\(session.role.rawValue)',\(session.createdAt.timeIntervalSince1970),\(session.expiresAt.timeIntervalSince1970),\(session.isActive ? 1 : 0));
        """
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Get session by ID
    /// - Parameter sessionId: Session ID to lookup
    /// - Returns: Session if found, nil otherwise
    public func getSession(sessionId: String) async throws -> Session? {
        let sql = "SELECT session_id,username,role,created_at,expires_at,is_active FROM \(schema).sessions WHERE session_id = '\(escape(sessionId))' LIMIT 1;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        guard let row = result.rows.first else { return nil }
        let role = UserRole(rawValue: str(row["role"]) ?? "user") ?? .user
        let createdAt = Date(timeIntervalSince1970: dbl(row["created_at"]) ?? 0)
        let expiresAt = Date(timeIntervalSince1970: dbl(row["expires_at"]) ?? 0)
        let isActive = (int(row["is_active"]) ?? 0) != 0
        return Session(sessionId: str(row["session_id"]) ?? sessionId, username: str(row["username"]) ?? "", role: role, createdAt: createdAt, expiresAt: expiresAt, isActive: isActive)
    }
    
    /// Delete session by ID
    /// - Parameter sessionId: Session ID to delete
    public func deleteSession(sessionId: String) async throws {
        let sql = "DELETE FROM \(schema).sessions WHERE session_id = '\(escape(sessionId))';"
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    /// Clean up expired sessions
    /// - Parameter now: Current timestamp for expiration check
    public func cleanupExpiredSessions(now: Date) async throws {
        let ts = now.timeIntervalSince1970
        let sql = "DELETE FROM \(schema).sessions WHERE expires_at <= \(ts);"
        _ = try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    // MARK: - Private Helpers
    
    /// Escape SQL string to prevent injection
    /// - Parameter s: String to escape
    /// - Returns: Escaped string
    private func escape(_ s: String) -> String {
        return s.replacingOccurrences(of: "'", with: "''")
    }
    
    // Value extractors
    private func str(_ v: Value?) -> String? {
        guard let v else { return nil }
        switch v {
        case .string(let s): return s
        case .int(let i): return String(i)
        case .double(let d): return String(d)
        case .bool(let b): return b ? "1" : "0"
        case .decimal(let dec): return "\(dec)"
        case .date(let date): return String(date.timeIntervalSince1970)
        case .bytes(let data): return data.base64EncodedString()
        case .null: return nil
        }
    }
    private func dbl(_ v: Value?) -> Double? {
        guard let v else { return nil }
        switch v {
        case .double(let d): return d
        case .int(let i): return Double(i)
        case .string(let s): return Double(s)
        default: return nil
        }
    }
    private func int(_ v: Value?) -> Int? {
        guard let v else { return nil }
        switch v {
        case .int(let i): return Int(i)
        case .bool(let b): return b ? 1 : 0
        case .string(let s): return Int(s)
        default: return nil
        }
    }
}


