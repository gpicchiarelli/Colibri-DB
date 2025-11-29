//
//  SystemCatalogBootstrap.swift
//  ColibrìDB
//
//  Created by ColibrìDB Team on 2025-10-19.
//
//  Initializes the private system catalog schema and core sys_* tables.
//

import Foundation

/// System catalog bootstrap actor
/// Initializes the private system catalog schema and core sys_* tables
public actor SystemCatalogBootstrap {
    // MARK: - Properties
    
    private let schema: String = "colibri_sys" // private, DBA-only
    
    // MARK: - Initialization
    
    /// Initialize system catalog bootstrap
    public init() {}
    
    // MARK: - Public Methods
    
    /// Initialize system catalog on database
    /// Creates all necessary system tables and schemas
    /// - Parameter db: Database instance to initialize
    public func initialize(on db: ColibrìDB) async throws {
        let tx = try await db.beginTransaction()
        do {
            // Private schema
            _ = try await db.executeQuery("CREATE SCHEMA IF NOT EXISTS \(schema);", txId: tx)
            
            // Core system tables (minimal viable set; extend as engine evolves)
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_users (
              user_id BIGINT PRIMARY KEY,
              username TEXT NOT NULL UNIQUE,
              email TEXT NULL,
              password_hash TEXT NOT NULL,
              password_salt TEXT NOT NULL,
              status TEXT NOT NULL,
              created_at DOUBLE NOT NULL,
              last_login DOUBLE NULL
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_roles (
              role_id BIGINT PRIMARY KEY,
              name TEXT NOT NULL UNIQUE,
              is_builtin INTEGER NOT NULL,
              created_at DOUBLE NOT NULL
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_role_members (
              role_id BIGINT NOT NULL,
              member_role_id BIGINT NOT NULL,
              PRIMARY KEY (role_id, member_role_id)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_databases (
              database_id BIGINT PRIMARY KEY,
              name TEXT NOT NULL UNIQUE,
              owner_user_id BIGINT NOT NULL,
              tablespace_id BIGINT NULL,
              is_system INTEGER NOT NULL,
              created_at DOUBLE NOT NULL
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_schemas (
              schema_id BIGINT PRIMARY KEY,
              database_id BIGINT NOT NULL,
              name TEXT NOT NULL,
              owner_user_id BIGINT NOT NULL,
              created_at DOUBLE NOT NULL,
              UNIQUE (database_id, name)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_tables (
              table_id BIGINT PRIMARY KEY,
              schema_id BIGINT NOT NULL,
              name TEXT NOT NULL,
              owner_user_id BIGINT NOT NULL,
              table_kind TEXT NOT NULL,
              options TEXT NULL,
              created_at DOUBLE NOT NULL,
              UNIQUE (schema_id, name)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_columns (
              column_id BIGINT PRIMARY KEY,
              table_id BIGINT NOT NULL,
              name TEXT NOT NULL,
              ordinal INT NOT NULL,
              data_type TEXT NOT NULL,
              nullable INTEGER NOT NULL,
              default_expr TEXT NULL,
              collation TEXT NULL,
              generated_kind TEXT NULL,
              UNIQUE (table_id, name),
              UNIQUE (table_id, ordinal)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_indexes (
              index_id BIGINT PRIMARY KEY,
              table_id BIGINT NOT NULL,
              name TEXT NOT NULL,
              is_unique INTEGER NOT NULL,
              is_primary INTEGER NOT NULL,
              method TEXT NOT NULL,
              options TEXT NULL,
              created_at DOUBLE NOT NULL,
              UNIQUE (table_id, name)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_index_columns (
              index_id BIGINT NOT NULL,
              column_id BIGINT NOT NULL,
              ordinal INT NOT NULL,
              "order" TEXT NOT NULL,
              nulls TEXT NOT NULL,
              PRIMARY KEY (index_id, ordinal)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_constraints (
              constraint_id BIGINT PRIMARY KEY,
              table_id BIGINT NOT NULL,
              name TEXT NOT NULL,
              constraint_type TEXT NOT NULL,
              check_expr TEXT NULL,
              referenced_table_id BIGINT NULL,
              match_type TEXT NULL,
              on_update TEXT NULL,
              on_delete TEXT NULL,
              UNIQUE (table_id, name)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_constraint_columns (
              constraint_id BIGINT NOT NULL,
              column_id BIGINT NOT NULL,
              ordinal INT NOT NULL,
              referenced_column_id BIGINT NULL,
              PRIMARY KEY (constraint_id, ordinal)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_privileges (
              privilege_id BIGINT PRIMARY KEY,
              grantee_kind TEXT NOT NULL,
              grantee_id BIGINT NOT NULL,
              object_type TEXT NOT NULL,
              object_id BIGINT NOT NULL,
              privilege_type TEXT NOT NULL,
              grantor_id BIGINT NOT NULL,
              grant_option INTEGER NOT NULL,
              UNIQUE (grantee_kind, grantee_id, object_type, object_id, privilege_type)
            );
            """, txId: tx)
            
            _ = try await db.executeQuery("""
            CREATE TABLE IF NOT EXISTS \(schema).sys_settings (
              key TEXT PRIMARY KEY,
              value TEXT NOT NULL,
              scope TEXT NOT NULL,
              database_id BIGINT NULL
            );
            """, txId: tx)
            
            // Seed minimal rows if empty (system database entry)
            try await seedIfNeeded(on: db, tx: tx)
            
            try await db.commit(txId: tx)
        } catch {
            try? await db.abort(txId: tx)
            throw error
        }
    }
    
    private func seedIfNeeded(on db: ColibrìDB, tx: TxID) async throws {
        // Insert system database row if not present
        let q = try await db.executeQuery("SELECT 1 FROM \(schema).sys_databases WHERE name='colibri_sys' LIMIT 1;", txId: tx)
        if q.rows.isEmpty {
            let now = Date().timeIntervalSince1970
            // Reserve user_id 1 as built-in sys_dba if missing
            let uq = try await db.executeQuery("SELECT 1 FROM \(schema).sys_users WHERE user_id=1;", txId: tx)
            if uq.rows.isEmpty {
                _ = try await db.executeQuery("""
                INSERT INTO \(schema).sys_users (user_id, username, email, password_hash, password_salt, status, created_at, last_login)
                VALUES (1, 'sys_dba', NULL, '', '', 'ACTIVE', \(now), NULL);
                """, txId: tx)
            }
            _ = try await db.executeQuery("""
            INSERT INTO \(schema).sys_databases (database_id, name, owner_user_id, tablespace_id, is_system, created_at)
            VALUES (1, 'colibri_sys', 1, NULL, 1, \(now));
            """, txId: tx)
            // Create sys and information_schema logical entries
            _ = try await db.executeQuery("""
            INSERT INTO \(schema).sys_schemas (schema_id, database_id, name, owner_user_id, created_at)
            VALUES (1, 1, 'sys', 1, \(now))
            ON CONFLICT (database_id, name) DO NOTHING;
            """, txId: tx)
            _ = try await db.executeQuery("""
            INSERT INTO \(schema).sys_schemas (schema_id, database_id, name, owner_user_id, created_at)
            VALUES (2, 1, 'information_schema', 1, \(now))
            ON CONFLICT (database_id, name) DO NOTHING;
            """, txId: tx)
            // Settings baseline
            _ = try await db.executeQuery("""
            INSERT INTO \(schema).sys_settings (key, value, scope, database_id)
            VALUES ('catalog_version','1','GLOBAL',NULL)
            ON CONFLICT (key) DO NOTHING;
            """, txId: tx)
        }
    }
}


