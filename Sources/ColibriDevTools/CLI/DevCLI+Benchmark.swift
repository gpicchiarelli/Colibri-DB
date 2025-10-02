//
//  DevCLI+Benchmark.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Benchmark commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    @MainActor private static var benchmarkTools: BenchmarkTools?
    
    /// Handles benchmark-related commands
    @MainActor mutating func handleBenchmarkCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\benchmark sql") {
            handleBenchmarkSQL(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark constraints") {
            handleBenchmarkConstraints(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark types") {
            handleBenchmarkTypes(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark memory") {
            handleBenchmarkMemory(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark suite") {
            handleBenchmarkSuite(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark custom") {
            handleBenchmarkCustom(trimmed)
            return
        }
    }
    
    // MARK: - Benchmark Commands
    
    /// Benchmark SQL operations
    @MainActor private func handleBenchmarkSQL(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let iterations = Int(parts.first(where: { $0.hasPrefix("iterations=") })?.dropFirst("iterations=".count) ?? "1000") ?? 1000
        
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running SQL benchmarks with \(iterations) iterations...")
        
        // SQL Parsing Benchmark
        print("\n1. SQL Parsing Benchmark:")
        let parsingResult = Self.benchmarkTools!.benchmarkSQLParsing(iterations: iterations)
        print(BenchmarkReporter.generateReport(parsingResult))
        
        // SQL Execution Benchmark
        print("\n2. SQL Execution Benchmark:")
        let executionResult = Self.benchmarkTools!.benchmarkSQLExecution(iterations: iterations / 10)
        print(BenchmarkReporter.generateReport(executionResult))
    }
    
    /// Benchmark constraint operations
    @MainActor private func handleBenchmarkConstraints(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let iterations = Int(parts.first(where: { $0.hasPrefix("iterations=") })?.dropFirst("iterations=".count) ?? "1000") ?? 1000
        
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running constraint benchmarks with \(iterations) iterations...")
        
        let result = Self.benchmarkTools!.benchmarkConstraintValidation(iterations: iterations)
        print(BenchmarkReporter.generateReport(result))
    }
    
    /// Benchmark data type operations
    @MainActor private func handleBenchmarkTypes(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let iterations = Int(parts.first(where: { $0.hasPrefix("iterations=") })?.dropFirst("iterations=".count) ?? "10000") ?? 10000
        
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running data type operation benchmarks with \(iterations) iterations...")
        
        let result = Self.benchmarkTools!.benchmarkDataTypeOperations(iterations: iterations)
        print(BenchmarkReporter.generateReport(result))
    }
    
    /// Benchmark memory operations
    @MainActor private func handleBenchmarkMemory(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let iterations = Int(parts.first(where: { $0.hasPrefix("iterations=") })?.dropFirst("iterations=".count) ?? "100") ?? 100
        
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running memory allocation benchmarks with \(iterations) iterations...")
        print("Warning: This may use significant memory and take several minutes")
        
        let result = Self.benchmarkTools!.benchmarkMemoryAllocation(iterations: iterations)
        print(BenchmarkReporter.generateReport(result))
    }
    
    /// Run comprehensive benchmark suite
    @MainActor private func handleBenchmarkSuite(_ trimmed: String) {
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running comprehensive benchmark suite...")
        print("This will take several minutes to complete")
        
        let startTime = Date()
        let result = Self.benchmarkTools!.runBenchmarkSuite()
        let endTime = Date()
        
        print(BenchmarkReporter.generateSuiteReport(result))
        
        let totalDuration = endTime.timeIntervalSince(startTime)
        print("Total suite duration: \(String(format: "%.2f", totalDuration))s")
    }
    
    /// Run custom benchmark
    @MainActor private func handleBenchmarkCustom(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        guard parts.count >= 3 else {
            print("usage: \\benchmark custom <name> <iterations> <operation>")
            print("operations: table_ops, data_ops, index_ops, transaction_ops")
            return
        }
        
        let name = String(parts[1])
        let iterations = Int(parts[2]) ?? 1000
        let operation = parts.count > 3 ? String(parts[3]) : "table_ops"
        
        if Self.benchmarkTools == nil {
            Self.benchmarkTools = BenchmarkTools(database: db)
        }
        
        print("Running custom benchmark '\(name)' with \(iterations) iterations...")
        
        let result = Self.benchmarkTools!.runCustomBenchmark(
            name: name,
            iterations: iterations
        ) {
            try self.executeCustomOperation(operation)
        }
        
        print(BenchmarkReporter.generateReport(result))
    }
    
    // MARK: - Custom Operations
    
    private func executeCustomOperation(_ operation: String) throws {
        switch operation {
        case "table_ops":
            try executeTableOperations()
        case "data_ops":
            try executeDataOperations()
        case "index_ops":
            try executeIndexOperations()
        case "transaction_ops":
            try executeTransactionOperations()
        default:
            throw BenchmarkError.unknownOperation(operation)
        }
    }
    
    private func executeTableOperations() throws {
        // Create table
        try db.createTable("custom_benchmark")
        
        // TODO: Implement alterTable and dropTable methods in Database class
        // Alter table
        // try db.alterTable("custom_benchmark", operation: .addColumn("id", "int"))
        // try db.alterTable("custom_benchmark", operation: .addColumn("name", "string"))
        
        // Drop table
        // try db.dropTable("custom_benchmark")
    }
    
    private func executeDataOperations() throws {
        // Create table
        try db.createTable("custom_data_benchmark")
        
        // Insert data
        for i in 1...100 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("User \(i)")]
            _ = try db.insert(into: "custom_data_benchmark", row: row)
        }
        
        // Scan data
        _ = try db.scan("custom_data_benchmark")
        
        // Delete data
        for i in 1...100 {
            _ = try db.deleteEquals(table: "custom_data_benchmark", column: "id", value: .int(Int64(i)))
        }
        
        // TODO: Implement dropTable method in Database class
        // Drop table
        // try db.dropTable("custom_data_benchmark")
    }
    
    private func executeIndexOperations() throws {
        // Create table
        try db.createTable("custom_index_benchmark")
        
        // Insert data
        for i in 1...1000 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("User \(i)")]
            _ = try db.insert(into: "custom_index_benchmark", row: row)
        }
        
        // Create index
        try db.createIndex(name: "idx_id", on: "custom_index_benchmark", columns: ["id"], using: "Hash")
        
        // Search using index
        for i in 1...100 {
            _ = try db.indexSearchEqualsTyped(table: "custom_index_benchmark", index: "idx_id", value: .int(Int64(i)))
        }
        
        // TODO: Implement dropTable method in Database class
        // Drop table (index will be dropped automatically)
        // try db.dropTable("custom_index_benchmark")
    }
    
    private func executeTransactionOperations() throws {
        // Create table
        try db.createTable("custom_txn_benchmark")
        
        // Begin transaction
        let tid = try db.begin()
        
        // Insert data
        for i in 1...50 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("User \(i)")]
            _ = try db.insert(into: "custom_txn_benchmark", row: row, tid: tid)
        }
        
        // Commit transaction
        try db.commit(tid)
        
        // Begin another transaction
        let tid2 = try db.begin()
        
        // Update data
        for i in 1...50 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("Updated User \(i)")]
            _ = try db.insert(into: "custom_txn_benchmark", row: row, tid: tid2)
        }
        
        // Rollback transaction
        try db.rollback(tid2)
        
        // TODO: Implement dropTable method in Database class
        // Drop table
        // try db.dropTable("custom_txn_benchmark")
    }
}

// MARK: - Benchmark Error

public enum BenchmarkError: Error {
    case unknownOperation(String)
    
    public var localizedDescription: String {
        switch self {
        case .unknownOperation(let operation):
            return "Unknown benchmark operation: \(operation)"
        }
    }
}
