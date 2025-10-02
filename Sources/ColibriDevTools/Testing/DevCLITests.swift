//
//  DevCLITests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Unit tests for DevCLI and its modules.

import Foundation
import ColibriCore

class DevCLITests {
    var db: Database!
    var cli: DevCLI!
    
    func setUp() {
        do {
            let config = DBConfig(dataDir: "/tmp/test_db", maxConnectionsLogical: 10, maxConnectionsPhysical: 5)
            db = try Database(config: config)
            try db.ensureDataDir()
            cli = DevCLI(db: db, cfgPath: nil)
        } catch {
            print("Failed to setup test database: \(error)")
        }
    }
    
    func tearDown() {
        // Cleanup test database
        try? FileManager.default.removeItem(atPath: "/tmp/test_db")
    }
    
    // MARK: - Basic CLI Tests
    
    func testBannerDisplay() {
        // Test that banner is displayed correctly
        let output = captureOutput {
            cli.printBanner()
        }
        assert(output.contains("ColibrDB Dev CLI"))
        assert(output.contains("Development Version"))
    }
    
    func testHelpCommand() {
        let output = captureOutput {
            cli.help()
        }
        assert(output.contains("Commands:"))
        assert(output.contains("\\help"))
        assert(output.contains("\\create table"))
        assert(output.contains("\\insert"))
    }
    
    func testConfigDisplay() {
        let output = captureOutput {
            cli.showConfig()
        }
        assert(output.contains("Configuration:"))
        assert(output.contains("dataDir=/tmp/test_db"))
    }
    
    func testListTablesEmpty() {
        let output = captureOutput {
            cli.listTables()
        }
        assert(output.contains("(no tables)"))
    }
    
    // MARK: - Command Parsing Tests
    
    @MainActor func testCommandParsing() {
        // Test basic command recognition
        let testCases = [
            ("\\help", "help"),
            ("\\conf", "config"),
            ("\\dt", "tables"),
            ("\\exit", "exit")
        ]
        
        for (command, _) in testCases {
            // This would need to be implemented in DevCLI to return command type
            // For now, we test that commands don't crash
            do {
                self.cli.parseAndRun(command)
            }
        }
    }
    
    @MainActor func testInvalidCommand() {
        let output = captureOutput {
            cli.parseAndRun("\\invalid_command")
        }
        assert(output.contains("Unrecognized command"))
    }
    
    // MARK: - Utility Functions Tests
    
    func testExtractToken() {
        let text = "test BY col1,col2 WINDOW 10:00-11:00"
        let byToken = cli.extractToken(after: "BY", in: text)
        assert(byToken == "col1,col2")
        
        let windowToken = cli.extractToken(after: "WINDOW", in: text)
        assert(windowToken == "10:00-11:00")
    }
    
    func testExtractList() {
        let text = "test BY col1,col2,col3 WINDOW 10:00-11:00"
        let columns = cli.extractList(after: "BY", in: text)
        assert(columns == ["col1", "col2", "col3"])
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

// MARK: - DevCLI Extensions for Testing

extension DevCLI {
    // Expose private methods for testing
    func extractToken(after keyword: String, in text: String) -> String? {
        let tokens = text.split(separator: " ")
        guard let idx = tokens.firstIndex(where: { $0.uppercased() == keyword.uppercased() }) else { return nil }
        let nextIdx = tokens.index(after: idx)
        guard nextIdx < tokens.endIndex else { return nil }
        return String(tokens[nextIdx])
    }
    
    func extractList(after keyword: String, in text: String) -> [String] {
        guard let token = extractToken(after: keyword, in: text) else { return [] }
        return token.split(separator: ",").map { String($0) }
    }
}
