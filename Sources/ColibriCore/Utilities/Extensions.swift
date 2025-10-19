//
//  Extensions.swift
//

import Foundation

extension Value: Comparable {
    public static func < (lhs: Value, rhs: Value) -> Bool {
        switch (lhs, rhs) {
        case (.int(let a), .int(let b)):
            return a < b
        case (.double(let a), .double(let b)):
            return a < b
        case (.string(let a), .string(let b)):
            return a < b
        case (.date(let a), .date(let b)):
            return a < b
        case (.bool(let a), .bool(let b)):
            return !a && b
        case (.null, _):
            return true
        case (_, .null):
            return false
        default:
            return false
        }
    }
}

extension Data {
    func hexString() -> String {
        return map { String(format: "%02x", $0) }.joined()
    }
    
    init?(hexString: String) {
        var data = Data()
        var temp = ""
        
        for char in hexString {
            temp.append(char)
            if temp.count == 2 {
                guard let byte = UInt8(temp, radix: 16) else {
                    return nil
                }
                data.append(byte)
                temp = ""
            }
        }
        
        guard temp.isEmpty else {
            return nil
        }
        
        self = data
    }
}

extension Array {
    func chunked(into size: Int) -> [[Element]] {
        return stride(from: 0, to: count, by: size).map {
            Array(self[$0..<Swift.min($0 + size, count)])
        }
    }
}

extension Dictionary {
    mutating func merge(_ other: [Key: Value]) {
        for (key, value) in other {
            self[key] = value
        }
    }
}

extension Date {
    var millisecondsSince1970: Int64 {
        return Int64(timeIntervalSince1970 * 1000)
    }
    
    init(millisecondsSince1970: Int64) {
        self.init(timeIntervalSince1970: TimeInterval(millisecondsSince1970) / 1000.0)
    }
}

