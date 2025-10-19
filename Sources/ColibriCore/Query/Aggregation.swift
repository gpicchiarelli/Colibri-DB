//
//  Aggregation.swift
//  Based on: spec/Aggregation.tla
//

import Foundation

public actor AggregationExecutor {
    public init() {}
    
    public func count(_ rows: [Row]) -> Int {
        return rows.count
    }
    
    public func sum(_ rows: [Row], column: String) -> Value {
        var total: Double = 0
        
        for row in rows {
            if case .int(let val) = row[column] {
                total += Double(val)
            } else if case .double(let val) = row[column] {
                total += val
            }
        }
        
        return .double(total)
    }
    
    public func avg(_ rows: [Row], column: String) -> Value {
        guard !rows.isEmpty else { return .null }
        
        if case .double(let total) = sum(rows, column: column) {
            return .double(total / Double(rows.count))
        }
        
        return .null
    }
    
    public func min(_ rows: [Row], column: String) -> Value {
        var minValue: Value? = nil
        
        for row in rows {
            if let value = row[column] {
                if minValue == nil {
                    minValue = value
                } else if let min = minValue, compareValues(value, min) < 0 {
                    minValue = value
                }
            }
        }
        
        return minValue ?? .null
    }
    
    public func max(_ rows: [Row], column: String) -> Value {
        var maxValue: Value? = nil
        
        for row in rows {
            if let value = row[column] {
                if maxValue == nil {
                    maxValue = value
                } else if let max = maxValue, compareValues(value, max) > 0 {
                    maxValue = value
                }
            }
        }
        
        return maxValue ?? .null
    }
    
    public func groupBy(_ rows: [Row], columns: [String]) -> [[String: Value]: [Row]] {
        var groups: [[String: Value]: [Row]] = [:]
        
        for row in rows {
            var groupKey: [String: Value] = [:]
            for column in columns {
                groupKey[column] = row[column]
            }
            groups[groupKey, default: []].append(row)
        }
        
        return groups
    }
    
    private func compareValues(_ v1: Value, _ v2: Value) -> Int {
        switch (v1, v2) {
        case (.int(let a), .int(let b)):
            return a < b ? -1 : (a > b ? 1 : 0)
        case (.double(let a), .double(let b)):
            return a < b ? -1 : (a > b ? 1 : 0)
        case (.string(let a), .string(let b)):
            return a < b ? -1 : (a > b ? 1 : 0)
        default:
            return 0
        }
    }
}

