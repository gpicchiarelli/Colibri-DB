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
    
    func testHash64x2H2IsOddAndNonZero() {
        let v: Value = .string("odd-check")
        for seed in 0..<10 {
            let (_, h2) = HardwareHash.hash64x2(v, seed: UInt64(seed), backend: .sha256)
            XCTAssertNotEqual(h2, 0)
            XCTAssertEqual(h2 & 1, 1, "h2 should be odd")
        }
    }
    
    func testBackendsProduceDeterministicButDifferentHashes() {
        let v: Value = .string("backend-check")
        let s: UInt64 = 42
        let x1 = HardwareHash.hash64(v, seed: s, backend: .sha256)
        let x2 = HardwareHash.hash64(v, seed: s, backend: .sha256)
        XCTAssertEqual(x1, x2) // deterministic
        
        let y1 = HardwareHash.hash64(v, seed: s, backend: .xxhash64)
        let y2 = HardwareHash.hash64(v, seed: s, backend: .xxhash64)
        XCTAssertEqual(y1, y2) // deterministic
        
        // Not strictly required, but typically distinct across backends
        XCTAssertNotEqual(x1, y1, "Different backends should generally yield distinct hashes")
    }
}


