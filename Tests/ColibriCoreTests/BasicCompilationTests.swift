//
//  BasicCompilationTests.swift
//  ColibrìDB Tests
//
//  Author: ColibrìDB Team
//  Date: 2025-01-27
//

import XCTest
@testable import ColibriCore

/// Basic compilation tests to verify the project builds correctly
final class BasicCompilationTests: XCTestCase {
    
    /// Test that basic types can be instantiated
    func testBasicTypes() throws {
        // Test Value type
        let intValue = Value.int(42)
        XCTAssertEqual(intValue, .int(42))
        
        let stringValue = Value.string("test")
        XCTAssertEqual(stringValue, .string("test"))
        
        let nullValue = Value.null
        XCTAssertEqual(nullValue, .null)
    }
    
    /// Test that TxID type works
    func testTxID() throws {
        let txId: TxID = 123
        XCTAssertEqual(txId, 123)
    }
    
    /// Test that PageID type works
    func testPageID() throws {
        let pageId: PageID = 456
        XCTAssertEqual(pageId, 456)
    }
    
    /// Test that LSN type works
    func testLSN() throws {
        let lsn: LSN = 789
        XCTAssertEqual(lsn, 789)
    }
    
    /// Test that basic enums work
    func testEnums() throws {
        let logType = LogRecordType.update
        XCTAssertEqual(logType, .update)
        
        let orderType = SortKey.SortOrder.ascending
        XCTAssertEqual(orderType, .ascending)
    }
    
    /// Test that basic structs can be created
    func testBasicStructs() throws {
        let sortKey = SortKey(column: 0, order: .ascending)
        XCTAssertEqual(sortKey.column, 0)
        XCTAssertEqual(sortKey.order, .ascending)
    }
    
    /// Test that logging functions work
    func testLogging() throws {
        // This should not crash
        logInfo("Test log message", category: .general)
        logDebug("Test debug message", category: .general)
    }
}
