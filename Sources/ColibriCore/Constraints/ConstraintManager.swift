//
//  ConstraintManager.swift
//  ColibrìDB Constraint Manager
//
//  Based on: spec/ConstraintManager.tla
//  Implements: PRIMARY KEY, FOREIGN KEY, UNIQUE, CHECK constraints
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Constraint type
public enum ConstraintType {
    case primaryKey(columns: [String])
    case foreignKey(columns: [String], refTable: String, refColumns: [String], onDelete: ReferentialAction, onUpdate: ReferentialAction)
    case unique(columns: [String])
    case check(name: String, predicate: (Row) -> Bool)
    case notNull(column: String)
}

/// Referential action for foreign keys
public enum ReferentialAction {
    case noAction
    case cascade
    case setNull
    case setDefault
    case restrict
}

/// Constraint definition
public struct Constraint {
    public let name: String
    public let table: String
    public let type: ConstraintType
    
    public init(name: String, table: String, type: ConstraintType) {
        self.name = name
        self.table = table
        self.type = type
    }
}

/// Constraint Manager
/// Corresponds to TLA+ module: ConstraintManager.tla
public actor ConstraintManager {
    // MARK: - State
    
    /// All constraints
    private var constraints: [String: [Constraint]] = [:]  // table -> constraints
    
    /// Primary key indexes for fast lookup
    private var primaryKeyIndexes: [String: BTreeIndex] = [:]
    
    /// Unique indexes
    private var uniqueIndexes: [String: BTreeIndex] = [:]
    
    /// Foreign key relationships
    private var foreignKeyGraph: [String: Set<String>] = [:]  // parent -> children
    
    // MARK: - Initialization
    
    public init() {}
    
    // MARK: - Constraint Management
    
    /// Add constraint to table
    /// TLA+ Action: AddConstraint(table, constraint)
    public func addConstraint(_ constraint: Constraint) async throws {
        constraints[constraint.table, default: []].append(constraint)
        
        // Create index for primary key or unique
        switch constraint.type {
        case .primaryKey(let columns):
            primaryKeyIndexes[constraint.table] = BTreeIndex()
            
        case .unique(let columns):
            let indexName = "\(constraint.table)_\(constraint.name)_unique"
            uniqueIndexes[indexName] = BTreeIndex()
            
        case .foreignKey(_, let refTable, _, _, _):
            // Build foreign key graph
            foreignKeyGraph[refTable, default: []].insert(constraint.table)
            
        default:
            break
        }
    }
    
    /// Remove constraint
    public func removeConstraint(table: String, name: String) {
        constraints[table]?.removeAll { $0.name == name }
    }
    
    /// Get constraints for table
    public func getConstraints(table: String) -> [Constraint] {
        return constraints[table] ?? []
    }
    
    // MARK: - Constraint Validation
    
    /// Validate row before insert
    /// TLA+ Action: ValidateInsert(table, row, rid)
    public func validateInsert(table: String, row: Row, rid: RID, txID: TxID) async throws {
        guard let tableConstraints = constraints[table] else {
            return
        }
        
        for constraint in tableConstraints {
            switch constraint.type {
            case .primaryKey(let columns):
                try await validatePrimaryKey(table: table, columns: columns, row: row, rid: rid)
                
            case .foreignKey(let columns, let refTable, let refColumns, _, _):
                try await validateForeignKey(
                    columns: columns,
                    row: row,
                    refTable: refTable,
                    refColumns: refColumns
                )
                
            case .unique(let columns):
                try await validateUnique(table: table, constraint: constraint.name, columns: columns, row: row, rid: rid)
                
            case .check(let name, let predicate):
                if !predicate(row) {
                    throw DBError.checkConstraintViolation
                }
                
            case .notNull(let column):
                if row[column]?.isNull ?? true {
                    throw DBError.notNullViolation
                }
            }
        }
    }
    
    /// Validate row before update
    /// TLA+ Action: ValidateUpdate(table, oldRow, newRow, rid)
    public func validateUpdate(table: String, oldRow: Row, newRow: Row, rid: RID, txID: TxID) async throws {
        // Similar to insert validation
        try await validateInsert(table: table, row: newRow, rid: rid, txID: txID)
    }
    
    /// Validate before delete (check foreign keys)
    /// TLA+ Action: ValidateDelete(table, row, rid)
    public func validateDelete(table: String, row: Row, rid: RID, txID: TxID) async throws {
        // Check if any foreign keys reference this row
        guard let dependentTables = foreignKeyGraph[table] else {
            return
        }
        
        for dependentTable in dependentTables {
            let dependentConstraints = constraints[dependentTable] ?? []
            
            for constraint in dependentConstraints {
                if case .foreignKey(_, let refTable, let refColumns, let onDelete, _) = constraint.type,
                   refTable == table {
                    
                    // Check referential action
                    switch onDelete {
                    case .noAction, .restrict:
                        // Check if any rows reference this
                        // (simplified - would need to query dependent table)
                        throw DBError.foreignKeyViolation
                        
                    case .cascade:
                        // Will cascade delete (handled by caller)
                        break
                        
                    case .setNull:
                        // Will set foreign key to null (handled by caller)
                        break
                        
                    case .setDefault:
                        // Will set foreign key to default (handled by caller)
                        break
                    }
                }
            }
        }
    }
    
    // MARK: - Cascade Operations
    
    /// Perform cascade delete
    /// TLA+ Action: CascadeDelete(table, row)
    public func cascadeDelete(table: String, row: Row, txID: TxID) async throws -> [CascadeOperation] {
        var operations: [CascadeOperation] = []
        
        guard let dependentTables = foreignKeyGraph[table] else {
            return operations
        }
        
        for dependentTable in dependentTables {
            let dependentConstraints = constraints[dependentTable] ?? []
            
            for constraint in dependentConstraints {
                if case .foreignKey(let columns, let refTable, let refColumns, let onDelete, _) = constraint.type,
                   refTable == table {
                    
                    switch onDelete {
                    case .cascade:
                        operations.append(.delete(table: dependentTable, columns: columns))
                        
                    case .setNull:
                        operations.append(.setNull(table: dependentTable, columns: columns))
                        
                    case .setDefault:
                        operations.append(.setDefault(table: dependentTable, columns: columns))
                        
                    default:
                        break
                    }
                }
            }
        }
        
        return operations
    }
    
    /// Perform cascade update
    public func cascadeUpdate(table: String, oldRow: Row, newRow: Row, txID: TxID) async throws -> [CascadeOperation] {
        var operations: [CascadeOperation] = []
        
        guard let dependentTables = foreignKeyGraph[table] else {
            return operations
        }
        
        for dependentTable in dependentTables {
            let dependentConstraints = constraints[dependentTable] ?? []
            
            for constraint in dependentConstraints {
                if case .foreignKey(let columns, let refTable, let refColumns, _, let onUpdate) = constraint.type,
                   refTable == table {
                    
                    switch onUpdate {
                    case .cascade:
                        operations.append(.update(table: dependentTable, columns: columns, newValues: [:]))
                        
                    case .setNull:
                        operations.append(.setNull(table: dependentTable, columns: columns))
                        
                    case .setDefault:
                        operations.append(.setDefault(table: dependentTable, columns: columns))
                        
                    default:
                        break
                    }
                }
            }
        }
        
        return operations
    }
    
    // MARK: - Private Validation Helpers
    
    /// Validate primary key constraint
    private func validatePrimaryKey(table: String, columns: [String], row: Row, rid: RID) async throws {
        // Check not null
        for column in columns {
            if row[column]?.isNull ?? true {
                throw DBError.notNullViolation
            }
        }
        
        // Check uniqueness (simplified - would use index)
        guard let index = primaryKeyIndexes[table] else {
            throw DBError.internalError("Primary key index not found")
        }
        
        // Create composite key
        let keyValues = columns.compactMap { row[$0] }
        guard keyValues.count == columns.count else {
            throw DBError.notNullViolation
        }
        
        let compositeKey = Value.string(keyValues.map { "\($0)" }.joined(separator: "|"))
        
        // Check if key already exists
        if await index.search(key: compositeKey) != nil {
            throw DBError.uniqueViolation
        }
        
        // Insert into index
        try await index.insert(key: compositeKey, rid: rid)
    }
    
    /// Validate unique constraint
    private func validateUnique(table: String, constraint: String, columns: [String], row: Row, rid: RID) async throws {
        let indexName = "\(table)_\(constraint)_unique"
        
        guard let index = uniqueIndexes[indexName] else {
            throw DBError.internalError("Unique index not found")
        }
        
        // Create composite key
        let keyValues = columns.compactMap { row[$0] }
        let compositeKey = Value.string(keyValues.map { "\($0)" }.joined(separator: "|"))
        
        // Check if key already exists
        if await index.search(key: compositeKey) != nil {
            throw DBError.uniqueViolation
        }
        
        // Insert into index
        try await index.insert(key: compositeKey, rid: rid)
    }
    
    /// Validate foreign key constraint
    private func validateForeignKey(
        columns: [String],
        row: Row,
        refTable: String,
        refColumns: [String]
    ) async throws {
        // Check if referenced row exists (simplified)
        // In real implementation, would query the referenced table
        
        // For now, just check that foreign key values are not null
        for column in columns {
            if row[column]?.isNull ?? true {
                // Null foreign keys are allowed
                return
            }
        }
        
        // Would check: SELECT 1 FROM refTable WHERE refColumns = values
        // throw DBError.foreignKeyViolation if not found
    }
}

// MARK: - Supporting Types

/// Cascade operation to perform
public enum CascadeOperation {
    case delete(table: String, columns: [String])
    case update(table: String, columns: [String], newValues: Row)
    case setNull(table: String, columns: [String])
    case setDefault(table: String, columns: [String])
}

