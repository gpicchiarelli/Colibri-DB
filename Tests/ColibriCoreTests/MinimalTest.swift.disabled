import Foundation
import Testing
@testable import ColibriCore

/// Minimal test to isolate the crash issue
@Suite("Minimal Tests")
struct MinimalTest {
    
    @Test("Simple Test")
    func testSimple() throws {
        let value = 42
        try TestAssertions.assertEqual(value, 42, "Simple test should pass")
    }
    
    @Test("String Test")
    func testString() throws {
        let text = "Hello, World!"
        try TestAssertions.assertEqual(text, "Hello, World!", "String test should pass")
    }
}
