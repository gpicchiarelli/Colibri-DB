//
//  InformationSchemaViews.swift
//  SQL-standard INFORMATION_SCHEMA read-only views mapping sys_* tables
//

import Foundation

/// INFORMATION_SCHEMA view definitions (SQL-standard catalog views)
/// These views map sys_* tables to SQL-standard names for client compatibility
public struct InformationSchemaViews {
    private static let schema = "colibri_sys"
    
    /// Create all INFORMATION_SCHEMA views as CREATE VIEW statements
    /// Note: These are stored as view definitions; actual view creation requires parser support
    public static func getAllViewDefinitions() -> [String: String] {
        return [
            "schemata": schemataView,
            "tables": tablesView,
            "columns": columnsView,
            "table_constraints": tableConstraintsView,
            "key_column_usage": keyColumnUsageView,
            "referential_constraints": referentialConstraintsView
        ]
    }
    
    // MARK: - INFORMATION_SCHEMA.SCHEMATA
    
    /// SQL-standard: information_schema.schemata
    /// Maps to: sys_databases + sys_schemas
    private static let schemataView = """
        SELECT
            d.name AS catalog_name,
            s.name AS schema_name,
            u.username AS schema_owner,
            s.created_at AS created_at
        FROM \(schema).sys_schemas s
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        JOIN \(schema).sys_users u ON u.user_id = s.owner_user_id
        ORDER BY d.name, s.name;
    """
    
    // MARK: - INFORMATION_SCHEMA.TABLES
    
    /// SQL-standard: information_schema.tables
    /// Maps to: sys_tables
    private static let tablesView = """
        SELECT
            d.name AS table_catalog,
            s.name AS table_schema,
            t.name AS table_name,
            CASE
                WHEN t.table_kind = 'BASE' THEN 'BASE TABLE'
                WHEN t.table_kind = 'VIEW' THEN 'VIEW'
                WHEN t.table_kind = 'MATVIEW' THEN 'BASE TABLE'
                WHEN t.table_kind = 'SYS' THEN 'SYSTEM TABLE'
                ELSE 'BASE TABLE'
            END AS table_type,
            t.created_at AS created_at
        FROM \(schema).sys_tables t
        JOIN \(schema).sys_schemas s ON s.schema_id = t.schema_id
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        ORDER BY d.name, s.name, t.name;
    """
    
    // MARK: - INFORMATION_SCHEMA.COLUMNS
    
    /// SQL-standard: information_schema.columns
    /// Maps to: sys_columns
    private static let columnsView = """
        SELECT
            d.name AS table_catalog,
            s.name AS table_schema,
            t.name AS table_name,
            c.name AS column_name,
            c.ordinal AS ordinal_position,
            c.data_type AS data_type,
            CASE WHEN c.nullable = 1 THEN 'YES' ELSE 'NO' END AS is_nullable,
            c.default_expr AS column_default,
            c.collation AS collation_name,
            CASE WHEN c.generated_kind IS NOT NULL THEN 'YES' ELSE 'NO' END AS is_generated,
            c.generated_kind AS generation_expression
        FROM \(schema).sys_columns c
        JOIN \(schema).sys_tables t ON t.table_id = c.table_id
        JOIN \(schema).sys_schemas s ON s.schema_id = t.schema_id
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        ORDER BY d.name, s.name, t.name, c.ordinal;
    """
    
    // MARK: - INFORMATION_SCHEMA.TABLE_CONSTRAINTS
    
    /// SQL-standard: information_schema.table_constraints
    /// Maps to: sys_constraints
    private static let tableConstraintsView = """
        SELECT
            d.name AS constraint_catalog,
            s.name AS constraint_schema,
            c.name AS constraint_name,
            d.name AS table_catalog,
            s.name AS table_schema,
            t.name AS table_name,
            CASE c.constraint_type
                WHEN 'PRIMARY KEY' THEN 'PRIMARY KEY'
                WHEN 'UNIQUE' THEN 'UNIQUE'
                WHEN 'FOREIGN KEY' THEN 'FOREIGN KEY'
                WHEN 'CHECK' THEN 'CHECK'
                WHEN 'NOT NULL' THEN 'CHECK'
                ELSE c.constraint_type
            END AS constraint_type,
            CASE WHEN c.constraint_type = 'PRIMARY KEY' THEN 'NO' ELSE 'YES' END AS is_deferrable,
            'NO' AS initially_deferred
        FROM \(schema).sys_constraints c
        JOIN \(schema).sys_tables t ON t.table_id = c.table_id
        JOIN \(schema).sys_schemas s ON s.schema_id = t.schema_id
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        ORDER BY d.name, s.name, t.name, c.name;
    """
    
    // MARK: - INFORMATION_SCHEMA.KEY_COLUMN_USAGE
    
    /// SQL-standard: information_schema.key_column_usage
    /// Maps to: sys_constraint_columns
    private static let keyColumnUsageView = """
        SELECT
            d.name AS constraint_catalog,
            s.name AS constraint_schema,
            c.name AS constraint_name,
            d.name AS table_catalog,
            s.name AS table_schema,
            t.name AS table_name,
            col.name AS column_name,
            cc.ordinal AS ordinal_position,
            CASE WHEN c.constraint_type = 'PRIMARY KEY' THEN 1 ELSE NULL END AS position_in_unique_constraint
        FROM \(schema).sys_constraint_columns cc
        JOIN \(schema).sys_constraints c ON c.constraint_id = cc.constraint_id
        JOIN \(schema).sys_tables t ON t.table_id = c.table_id
        JOIN \(schema).sys_schemas s ON s.schema_id = t.schema_id
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        JOIN \(schema).sys_columns col ON col.column_id = cc.column_id
        ORDER BY d.name, s.name, t.name, c.name, cc.ordinal;
    """
    
    // MARK: - INFORMATION_SCHEMA.REFERENTIAL_CONSTRAINTS
    
    /// SQL-standard: information_schema.referential_constraints
    /// Maps to: sys_constraints (FK only) + referenced tables
    private static let referentialConstraintsView = """
        SELECT
            d.name AS constraint_catalog,
            s.name AS constraint_schema,
            c.name AS constraint_name,
            d.name AS unique_constraint_catalog,
            s.name AS unique_constraint_schema,
            rt.name AS unique_constraint_name,
            c.match_type AS match_option,
            c.on_update AS update_rule,
            c.on_delete AS delete_rule
        FROM \(schema).sys_constraints c
        JOIN \(schema).sys_tables t ON t.table_id = c.table_id
        JOIN \(schema).sys_schemas s ON s.schema_id = t.schema_id
        JOIN \(schema).sys_databases d ON d.database_id = s.database_id
        LEFT JOIN \(schema).sys_tables rt ON rt.table_id = c.referenced_table_id
        WHERE c.constraint_type = 'FOREIGN KEY'
        ORDER BY d.name, s.name, c.name;
    """
    
    /// Execute an INFORMATION_SCHEMA view query
    /// Returns the view definition SQL that can be executed
    public static func getViewQuery(viewName: String) -> String? {
        return getAllViewDefinitions()[viewName.lowercased()]
    }
    
    /// Check if a view name is a valid INFORMATION_SCHEMA view
    public static func isValidView(_ viewName: String) -> Bool {
        return getAllViewDefinitions().keys.contains(viewName.lowercased())
    }
}

