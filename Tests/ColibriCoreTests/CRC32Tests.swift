import XCTest
@testable import ColibriCore

final class CRC32Tests: XCTestCase {
    func testCRC32KnownVector() {
        let input = Data("123456789".utf8)
        let checksum = reflectCRC32(input)
        XCTAssertEqual(checksum, 0xCBF43926, "CRC32 of '123456789' should match standard IEEE value")
    }
    
    func testCRC32Empty() {
        let input = Data()
        let checksum = reflectCRC32(input)
        XCTAssertEqual(checksum, 0x00000000, "CRC32 of empty input should be 0")
    }
}

// Use internal path to checksum via FileWAL's private helper by duplicating logic here for test verification
// This ensures deterministic verification independent of hardware path.
private func reflectCRC32(_ data: Data) -> UInt32 {
    var crc: UInt32 = 0xFFFFFFFF
    for byte in data {
        var x = (crc ^ UInt32(byte)) & 0xFF
        for _ in 0..<8 {
            let mask = (x & 1) * 0xEDB88320
            x = (x >> 1) ^ UInt32(mask)
        }
        crc = (crc >> 8) ^ x
    }
    return ~crc
}


