//
//  DevCLITableTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Unit tests for table management commands.

import Foundation
import ColibriCore

class DevCLITableTests {
    var db: Database!
    var cli: DevCLI!
    
    func setUp() {
        do {
            let config = DBConfig(dataDir: "/tmp/test_db_tables", maxConnectionsLogical: 10, maxConnectionsPhysical: 5)
            db = try Database(config: config)
            try db.ensureDataDir()
            cli = DevCLI(db: db, cfgPath: nil)
        } catch {
            print("Failed to setup test database: \(error)")
        }
    }
    
    func tearDown() {
        try? FileManager.default.removeItem(atPath: "/tmp/test_db_tables")
    }
    
    // MARK: - Table Creation Tests
    
    func testCreateTable() {
        let output = captureOutput {
            cli.parseAndRun("\\create table test_table")
        }
        assert(output.contains("created test_table"))
        
        // Verify table exists
        let tables = db.listTables()
        assert(tables.contains("test_table"))
    }
    
    func testCreateTableInvalidCommand() {
        let output = captureOutput {
            cli.parseAndRun("\\create table")
        }
        // Should not crash, but may not create table
        assert(!output.contains("created"))
    }
    
    func testCreateDuplicateTable() {
        // Create first table
        cli.parseAndRun("\\create table test_table")
        
        // Try to create duplicate
        let output = captureOutput {
            cli.parseAndRun("\\create table test_table")
        }
        assert(output.contains("error"))
    }
    
    // MARK: - Table Deletion Tests
    
    func testDropTable() {
        // Create table first
        cli.parseAndRun("\\create table test_table")
        
        let output = captureOutput {
            cli.parseAndRun("\\drop table test_table")
        }
        assert(output.contains("dropped test_table"))
        
        // Verify table is gone
        let tables = db.listTables()
        assert(!tables.contains("test_table"))
    }
    
    func testDropNonExistentTable() {
        let output = captureOutput {
            cli.parseAndRun("\\drop table non_existent")
        }
        assert(output.contains("error"))
    }
    
    // MARK: - Table Alteration Tests
    
    func testAlterTableRename() {
        // Create table first
        cli.parseAndRun("\\create table test_table")
        
        let output = captureOutput {
            cli.parseAndRun("\\alter table test_table rename new_table")
        }
        assert(output.contains("renamed test_table to new_table"))
        
        // Verify rename
        let tables = db.listTables()
        assert(!tables.contains("test_table"))
        assert(tables.contains("new_table"))
    }
    
    func testAlterTableAddColumn() {
        // Create table first
        cli.parseAndRun("\\create table test_table")
        
        let output = captureOutput {
            cli.parseAndRun("\\alter table test_table add new_column string")
        }
        assert(output.contains("added column new_column string to test_table"))
    }
    
    func testAlterTableDropColumn() {
        // Create table and add column first
        cli.parseAndRun("\\create table test_table")
        cli.parseAndRun("\\alter table test_table add new_column string")
        
        let output = captureOutput {
            cli.parseAndRun("\\alter table test_table drop new_column")
        }
        assert(output.contains("dropped column new_column from test_table"))
    }
    
    func testAlterTableInvalidOperation() {
        cli.parseAndRun("\\create table test_table")
        
        let output = captureOutput {
            cli.parseAndRun("\\alter table test_table invalid_op")
        }
        assert(output.contains("usage:"))
    }
    
    // MARK: - Helper Methods
    
    private func captureOutput(_ block: () -> Void) -> String {
        let pipe = Pipe()
        let originalStdout = dup(fileno(stdout))
        
        dup2(pipe.fileHandleForWriting.fileDescriptor, fileno(stdout))
        
        block()
        
        fflush(stdout)
        dup2(originalStdout, fileno(stdout))
        close(originalStdout)
        
        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        return String(data: data, encoding: .utf8) ?? ""
    }
}
