//
//  DevCLIDataTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Unit tests for data manipulation commands.

import Foundation
import ColibriCore

class DevCLIDataTests {
    var db: Database!
    var cli: DevCLI!
    
    func setUp() {
        do {
            let config = DBConfig(dataDir: "/tmp/test_db_data", maxConnectionsLogical: 10, maxConnectionsPhysical: 5)
            db = try Database(config: config)
            try db.ensureDataDir()
            cli = DevCLI(db: db, cfgPath: nil)
            
            // Create test table
            try db.createTable("test_table")
        } catch {
            print("Failed to setup test database: \(error)")
        }
    }
    
    func tearDown() {
        try? FileManager.default.removeItem(atPath: "/tmp/test_db_data")
    }
    
    // MARK: - Insert Tests
    
    func testInsertSingleValue() {
        let output = captureOutput {
            cli.parseAndRun("\\insert test_table name=John")
        }
        assert(output.contains("inserted"))
    }
    
    func testInsertMultipleValues() {
        let output = captureOutput {
            cli.parseAndRun("\\insert test_table name=John,age=30,city=NewYork")
        }
        assert(output.contains("inserted"))
    }
    
    func testInsertWithDifferentTypes() {
        let output = captureOutput {
            cli.parseAndRun("\\insert test_table name=John,age=30,active=true,score=95.5")
        }
        assert(output.contains("inserted"))
    }
    
    func testInsertWithNull() {
        let output = captureOutput {
            cli.parseAndRun("\\insert test_table name=John,age=NULL")
        }
        assert(output.contains("inserted"))
    }
    
    func testInsertInvalidCommand() {
        let output = captureOutput {
            cli.parseAndRun("\\insert test_table")
        }
        assert(output.contains("usage:"))
    }
    
    // MARK: - Scan Tests
    
    func testScanEmptyTable() {
        let output = captureOutput {
            cli.parseAndRun("\\scan test_table")
        }
        assert(output.contains("(empty)"))
    }
    
    func testScanWithData() {
        // Insert some data first
        cli.parseAndRun("\\insert test_table name=John,age=30")
        cli.parseAndRun("\\insert test_table name=Jane,age=25")
        
        let output = captureOutput {
            cli.parseAndRun("\\scan test_table")
        }
        assert(output.contains("name=John"))
        assert(output.contains("name=Jane"))
        assert(!output.contains("(empty)"))
    }
    
    // MARK: - Delete Tests
    
    func testDeleteSingleCondition() {
        // Insert data first
        cli.parseAndRun("\\insert test_table name=John,age=30")
        cli.parseAndRun("\\insert test_table name=Jane,age=25")
        
        let output = captureOutput {
            cli.parseAndRun("\\delete test_table name=John")
        }
        assert(output.contains("deleted 1"))
    }
    
    func testDeleteMultipleConditions() {
        // Insert data first
        cli.parseAndRun("\\insert test_table name=John,age=30,city=NYC")
        cli.parseAndRun("\\insert test_table name=Jane,age=25,city=LA")
        
        let output = captureOutput {
            cli.parseAndRun("\\delete test_table name=John,age=30")
        }
        assert(output.contains("deleted 1"))
    }
    
    func testDeleteNoMatches() {
        cli.parseAndRun("\\insert test_table name=John,age=30")
        
        let output = captureOutput {
            cli.parseAndRun("\\delete test_table name=NonExistent")
        }
        assert(output.contains("deleted 0"))
    }
    
    func testDeleteInvalidCommand() {
        let output = captureOutput {
            cli.parseAndRun("\\delete test_table")
        }
        assert(output.contains("usage:"))
    }
    
    // MARK: - Value Parsing Tests
    
    func testParseValueString() {
        let value = cli.parseValue("hello")
        assert(value == .string("hello"))
    }
    
    func testParseValueInt() {
        let value = cli.parseValue("42")
        assert(value == .int(42))
    }
    
    func testParseValueDouble() {
        let value = cli.parseValue("3.14")
        assert(value == .double(3.14))
    }
    
    func testParseValueBool() {
        let trueValue = cli.parseValue("true")
        assert(trueValue == .bool(true))
        
        let falseValue = cli.parseValue("false")
        assert(falseValue == .bool(false))
    }
    
    func testParseValueNull() {
        let value = cli.parseValue("NULL")
        assert(value == .null)
    }
    
    func testParseValueDecimal() {
        let value = cli.parseValue("123.45d")
        if case .decimal(let decimal) = value {
            assert(decimal.description == "123.45")
        } else {
            print("Expected decimal value")
        }
    }
    
    func testParseValueDate() {
        let value = cli.parseValue("'2023-01-01T00:00:00Z'")
        if case .date(let date) = value {
            assert(date != nil)
        } else {
            print("Expected date value")
        }
    }
    
    func testParseValueJSON() {
        let value = cli.parseValue("j:{\"key\":\"value\"}")
        if case .json(let data) = value {
            assert(data != nil)
        } else {
            print("Expected JSON value")
        }
    }
    
    func testParseValueBlob() {
        let value = cli.parseValue("b:SGVsbG8gV29ybGQ=") // "Hello World" in base64
        if case .blob(let data) = value {
            assert(data != nil)
        } else {
            print("Expected BLOB value")
        }
    }
    
    func testParseValueEnum() {
        let value = cli.parseValue("e:Status.ACTIVE")
        if case .enumValue(let enumName, let enumValue) = value {
            assert(enumName == "Status")
            assert(enumValue == "ACTIVE")
        } else {
            print("Expected enum value")
        }
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

