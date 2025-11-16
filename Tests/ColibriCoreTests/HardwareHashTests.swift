import XCTest
@testable import ColibriCore

final class HardwareHashTests: XCTestCase {
    func testDeterministicAcrossRuns() {
        let v1: Value = .string("apple")
        let v2: Value = .int(42)
        let seed: UInt64 = 12345
        
        let h1a = HardwareHash.hash64(v1, seed: seed)
        let h1b = HardwareHash.hash64(v1, seed: seed)
        XCTAssertEqual(h1a, h1b)
        
        let h2a = HardwareHash.hash64(v2, seed: seed)
        let h2b = HardwareHash.hash64(v2, seed: seed)
        XCTAssertEqual(h2a, h2b)
    }
    
    func testDifferentSeedsProduceDifferentHashes() {
        let v: Value = .string("colibridb")
        let h1 = HardwareHash.hash64(v, seed: 1)
        let h2 = HardwareHash.hash64(v, seed: 2)
        XCTAssertNotEqual(h1, h2)
    }
}


