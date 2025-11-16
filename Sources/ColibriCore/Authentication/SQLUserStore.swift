//
//  SQLUserStore.swift
//  SQL-backed persistence for users and sessions
//

import Foundation

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

public actor SQLUserStore: UserStore {
    private let db: ColibrìDB
    private let schema: String = "colibri_sys"
    
    public init(database: ColibrìDB) {
        self.db = database
    }
    
    public func initializeSchema() async throws {
        // Create private schema for server
        try await db.executeQuery("CREATE SCHEMA IF NOT EXISTS \(schema);", txId: try await db.beginTransaction())
        
        // Users table
        try await db.executeQuery("""
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
        try await db.executeQuery("""
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
        try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).server_settings (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
        """, txId: try await db.beginTransaction())
    }
    
    // MARK: - Users
    public func createUser(_ user: UserMetadata) async throws {
        let ts = user.createdAt.timeIntervalSince1970
        let ll = user.lastLogin?.timeIntervalSince1970
        let lastLoginString = ll != nil ? "\(ll!)" : "NULL"
        let sql = """
            INSERT INTO \(schema).users (username, email, role, status, created_at, last_login, password_hash, salt)
            VALUES ('\(escape(user.username))','\(escape(user.email))','\(user.role.rawValue)','\(user.status.rawValue)',\(ts),\(lastLoginString),'\(escape(user.passwordHash))','\(escape(user.salt))');
        """
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func getUser(username: String) async throws -> UserMetadata? {
        let sql = "SELECT username,email,role,status,created_at,last_login,password_hash,salt FROM \(schema).users WHERE username = '\(escape(username))' LIMIT 1;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        guard let row = result.rows.first else { return nil }
        let role = UserRole(rawValue: row["role"]?.stringValue ?? "user") ?? .user
        let status = UserStatus(rawValue: row["status"]?.stringValue ?? "active") ?? .active
        let createdAt = Date(timeIntervalSince1970: row["created_at"]?.doubleValue ?? 0)
        let lastLogin: Date? = row["last_login"]?.doubleValue != nil ? Date(timeIntervalSince1970: row["last_login"]!.doubleValue!) : nil
        return UserMetadata(
            username: row["username"]?.stringValue ?? username,
            email: row["email"]?.stringValue ?? "",
            role: role,
            status: status,
            createdAt: createdAt,
            lastLogin: lastLogin,
            passwordHash: row["password_hash"]?.stringValue ?? "",
            salt: row["salt"]?.stringValue ?? ""
        )
    }
    
    public func getAllUsers() async throws -> [UserMetadata] {
        let sql = "SELECT username,email,role,status,created_at,last_login,password_hash,salt FROM \(schema).users;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        return result.rows.map { row in
            let role = UserRole(rawValue: row["role"]?.stringValue ?? "user") ?? .user
            let status = UserStatus(rawValue: row["status"]?.stringValue ?? "active") ?? .active
            let createdAt = Date(timeIntervalSince1970: row["created_at"]?.doubleValue ?? 0)
            let lastLogin: Date? = row["last_login"]?.doubleValue != nil ? Date(timeIntervalSince1970: row["last_login"]!.doubleValue!) : nil
            return UserMetadata(
                username: row["username"]?.stringValue ?? "",
                email: row["email"]?.stringValue ?? "",
                role: role,
                status: status,
                createdAt: createdAt,
                lastLogin: lastLogin,
                passwordHash: row["password_hash"]?.stringValue ?? "",
                salt: row["salt"]?.stringValue ?? ""
            )
        }
    }
    
    public func updateUserRole(username: String, newRole: UserRole) async throws {
        let sql = "UPDATE \(schema).users SET role = '\(newRole.rawValue)' WHERE username = '\(escape(username))';"
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func updatePassword(username: String, passwordHash: String, salt: String) async throws {
        let sql = "UPDATE \(schema).users SET password_hash = '\(escape(passwordHash))', salt = '\(escape(salt))' WHERE username = '\(escape(username))';"
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func updateLastLogin(username: String, at: Date) async throws {
        let ts = at.timeIntervalSince1970
        let sql = "UPDATE \(schema).users SET last_login = \(ts) WHERE username = '\(escape(username))';"
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func deleteUser(username: String) async throws {
        let sql1 = "DELETE FROM \(schema).sessions WHERE username = '\(escape(username))';"
        let sql2 = "DELETE FROM \(schema).users WHERE username = '\(escape(username))';"
        let tx = try await db.beginTransaction()
        try await db.executeQuery(sql1, txId: tx)
        try await db.executeQuery(sql2, txId: tx)
        try await db.commit(txId: tx)
    }
    
    // MARK: - Sessions
    public func createSession(_ session: Session) async throws {
        let sql = """
            INSERT INTO \(schema).sessions (session_id,username,role,created_at,expires_at,is_active)
            VALUES ('\(escape(session.sessionId))','\(escape(session.username))','\(session.role.rawValue)',\(session.createdAt.timeIntervalSince1970),\(session.expiresAt.timeIntervalSince1970),\(session.isActive ? 1 : 0));
        """
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func getSession(sessionId: String) async throws -> Session? {
        let sql = "SELECT session_id,username,role,created_at,expires_at,is_active FROM \(schema).sessions WHERE session_id = '\(escape(sessionId))' LIMIT 1;"
        let result = try await db.executeQuery(sql, txId: try await db.beginTransaction())
        guard let row = result.rows.first else { return nil }
        let role = UserRole(rawValue: row["role"]?.stringValue ?? "user") ?? .user
        let createdAt = Date(timeIntervalSince1970: row["created_at"]?.doubleValue ?? 0)
        let expiresAt = Date(timeIntervalSince1970: row["expires_at"]?.doubleValue ?? 0)
        let isActive = (row["is_active"]?.intValue ?? 0) != 0
        return Session(sessionId: row["session_id"]?.stringValue ?? sessionId, username: row["username"]?.stringValue ?? "", role: role, createdAt: createdAt, expiresAt: expiresAt, isActive: isActive)
    }
    
    public func deleteSession(sessionId: String) async throws {
        let sql = "DELETE FROM \(schema).sessions WHERE session_id = '\(escape(sessionId))';"
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    public func cleanupExpiredSessions(now: Date) async throws {
        let ts = now.timeIntervalSince1970
        let sql = "DELETE FROM \(schema).sessions WHERE expires_at <= \(ts);"
        try await db.executeQuery(sql, txId: try await db.beginTransaction())
    }
    
    // MARK: - Helpers
    private func escape(_ s: String) -> String {
        return s.replacingOccurrences(of: "'", with: "''")
    }
}


