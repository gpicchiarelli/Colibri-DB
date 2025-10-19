//
//  PreparedStatements.swift
//  Based on: spec/PreparedStatements.tla
//

import Foundation

public struct PreparedStatement {
    public let id: UUID
    public let sql: String
    public let parameterCount: Int
    public let createdAt: Date
    
    public init(sql: String, parameterCount: Int) {
        self.id = UUID()
        self.sql = sql
        self.parameterCount = parameterCount
        self.createdAt = Date()
    }
}

public actor PreparedStatementManager {
    private var statements: [UUID: PreparedStatement] = [:]
    private let maxStatements = 1000
    
    public init() {}
    
    public func prepare(sql: String) throws -> PreparedStatement {
        let parameterCount = sql.components(separatedBy: "?").count - 1
        
        let statement = PreparedStatement(sql: sql, parameterCount: parameterCount)
        
        if statements.count >= maxStatements {
            if let oldestId = statements.min(by: { $0.value.createdAt < $1.value.createdAt })?.key {
                statements[oldestId] = nil
            }
        }
        
        statements[statement.id] = statement
        
        return statement
    }
    
    public func execute(statementId: UUID, parameters: [Value]) async throws -> [Row] {
        guard let statement = statements[statementId] else {
            throw DBError.notFound
        }
        
        guard parameters.count == statement.parameterCount else {
            throw DBError.internalError("Parameter count mismatch")
        }
        
        return []
    }
    
    public func close(statementId: UUID) {
        statements[statementId] = nil
    }
    
    public func closeAll() {
        statements.removeAll()
    }
    
    public func getStatistics() -> PreparedStatementStatistics {
        return PreparedStatementStatistics(
            totalStatements: statements.count,
            maxStatements: maxStatements
        )
    }
}

public struct PreparedStatementStatistics {
    public let totalStatements: Int
    public let maxStatements: Int
}

