import Foundation
#if canImport(CRC32Accelerator)
import CRC32Accelerator
#endif

/// CRC32 helper offering hardware acceleration when the platform provides it.
enum CRC32 {
    private static let polynomialTable: [UInt32] = {
        (0..<256).map { i -> UInt32 in
            var c = UInt32(i)
            for _ in 0..<8 {
                c = (c & 1) != 0 ? (0xEDB88320 ^ (c >> 1)) : (c >> 1)
            }
            return c
        }
    }()

    private static func software(_ buffer: UnsafeRawBufferPointer) -> UInt32 {
        var crc: UInt32 = 0xFFFFFFFF
        for byte in buffer {
            let idx = Int((crc ^ UInt32(byte)) & 0xFF)
            crc = (crc >> 8) ^ polynomialTable[idx]
        }
        return crc ^ 0xFFFFFFFF
    }

    private static func hardware(_ buffer: UnsafeRawBufferPointer) -> UInt32? {
#if canImport(CRC32Accelerator)
        guard let base = buffer.baseAddress, !buffer.isEmpty else {
            return 0xFFFFFFFF ^ 0xFFFFFFFF // CRC of empty payload
        }
        var used: Int32 = 0
        let crc = crc32_accelerated(0xFFFFFFFF, base.assumingMemoryBound(to: UInt8.self), buffer.count, &used)
        return used == 1 ? crc : nil
#else
        return nil
#endif
    }

    static func compute(_ data: Data) -> UInt32 {
        data.withUnsafeBytes { bytes in
            compute(bytes)
        }
    }

    static func compute(_ buffer: UnsafeRawBufferPointer) -> UInt32 {
        if buffer.isEmpty {
            return 0
        }
        if let hw = hardware(buffer) {
            return hw
        }
        return software(buffer)
    }

    static func computeWithZeroedChecksum(data: inout Data, checksumOffset: Int) -> UInt32 {
        var copy = data
        copy.replaceSubrange(checksumOffset..<checksumOffset+4, with: [0,0,0,0])
        return copy.withUnsafeBytes { compute($0) }
    }

    static func verify(data: Data, checksumOffset: Int) -> Bool {
        var copy = data
        let stored = copy.subdata(in: checksumOffset..<checksumOffset+4).withUnsafeBytes { $0.load(as: UInt32.self) }
        copy.replaceSubrange(checksumOffset..<checksumOffset+4, with: [0,0,0,0])
        return copy.withUnsafeBytes { compute($0) } == stored
    }
}
