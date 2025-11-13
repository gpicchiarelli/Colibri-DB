import Foundation
import XCTest
@testable import ColibriCore

/// Minimal test to isolate the crash issue
final class MinimalTest {
    
    func testSimple() throws {
        let value = 42
        XCTAssertEqual(value, 42, "Simple test should pass")
    }
    
    func testString() throws {
        let text = "Hello, World!"
        XCTAssertEqual(text, "Hello, World!", "String test should pass")
    }
}

