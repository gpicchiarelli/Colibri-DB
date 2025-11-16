import XCTest
@testable import ColibriCore

final class BloomFilterHashTests: XCTestCase {
    func testBloomFilterDeterminism() {
        var bf1 = BloomFilter(size: 1024, hashCount: 3)
        var bf2 = BloomFilter(size: 1024, hashCount: 3)
        let values: [Value] = [.string("a"), .int(10), .bool(true), .double(3.14)]
        for v in values { bf1.insert(v); bf2.insert(v) }
        for v in values {
            XCTAssertEqual(bf1.contains(v), bf2.contains(v))
        }
    }
    
    func testBloomFilterIndexingWithDoubleHashing() {
        var bf = BloomFilter(size: 2048, hashCount: 5)
        let values: [Value] = (0..<100).map { .int($0) }
        for v in values { bf.insert(v) }
        // FPR should be reasonable for given m,n,k (not asserting exact bound, but sanity check)
        let fpr = bf.falsePositiveRate(insertedCount: values.count)
        XCTAssertGreaterThan(fpr, 0.0)
        XCTAssertLessThan(fpr, 1.0)
        // Check that inserted values are likely present
        for v in values {
            XCTAssertTrue(bf.contains(v))
        }
    }
    
    func testObservedFPRWithinReasonableBound() {
        // Parameters
        let m = 10_000
        let k = 3
        let n = 1_000
        var bf = BloomFilter(size: m, hashCount: k)
        let inserted: [Value] = (0..<n).map { .string("v-\($0)") }
        for v in inserted { bf.insert(v) }
        
        // Estimate theoretical FPR
        let mD = Double(m), kD = Double(k), nD = Double(n)
        let expectedFPR = pow(1.0 - exp(-kD * nD / mD), kD)
        
        // Measure observed FPR over a disjoint set
        let testN = 10_000
        var falsePositives = 0
        for i in n..<(n + testN) {
            let v: Value = .string("v-\(i)")
            if bf.contains(v) { falsePositives += 1 }
        }
        let observed = Double(falsePositives) / Double(testN)
        
        // Allow generous tolerance to avoid flakiness in CI
        XCTAssertLessThanOrEqual(observed, expectedFPR * 1.8 + 0.01, "Observed FPR \(observed) too high vs expected \(expectedFPR)")
    }
}


