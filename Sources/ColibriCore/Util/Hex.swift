//
//  Hex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Hex utility crate formatting bytes for diagnostics.

import Foundation
/// Hex encoding/decoding helpers for Data.

extension Data {
    /// Returns lowercase hex string for this data.
    func hexString() -> String {
        return self.map { String(format: "%02x", $0) }.joined()
    }
    /// Parses a lowercase/uppercase hex string into Data.
    static func fromHex(_ s: String) -> Data? {
        let len = s.count
        if len % 2 != 0 { return nil }
        var data = Data(capacity: len/2)
        var idx = s.startIndex
        for _ in 0..<(len/2) {
            let next = s.index(idx, offsetBy: 2)
            let byteStr = s[idx..<next]
            if let b = UInt8(byteStr, radix: 16) { data.append(b) } else { return nil }
            idx = next
        }
        return data
    }
}

