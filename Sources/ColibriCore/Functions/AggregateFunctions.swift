//
//  AggregateFunctions.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Aggregate functions for SQL queries (COUNT, SUM, AVG, MIN, MAX).

import Foundation

/// Aggregate function types supported by the database
public enum AggregateFunction: String, CaseIterable {
    case count = "COUNT"
    case sum = "SUM"
    case avg = "AVG"
    case min = "MIN"
    case max = "MAX"
    
    public var description: String { rawValue }
}

/// Result of an aggregate function computation
public enum AggregateResult: Equatable {
    case count(Int)
    case sum(Value)
    case avg(Double)
    case min(Value)
    case max(Value)
    case null
    
    public var description: String {
        switch self {
        case .count(let n): return "\(n)"
        case .sum(let v): return v.description
        case .avg(let d): return String(d)
        case .min(let v): return v.description
        case .max(let v): return v.description
        case .null: return "NULL"
        }
    }
}

/// Aggregate function executor
public final class AggregateExecutor {
    
    /// Executes an aggregate function on a collection of values
    public static func execute(_ function: AggregateFunction, 
                              on values: [Value], 
                              column: String? = nil) -> AggregateResult {
        switch function {
        case .count:
            return executeCount(values, column: column)
        case .sum:
            return executeSum(values)
        case .avg:
            return executeAvg(values)
        case .min:
            return executeMin(values)
        case .max:
            return executeMax(values)
        }
    }
    
    /// Executes COUNT function
    private static func executeCount(_ values: [Value], column: String?) -> AggregateResult {
        if column != nil {
            // COUNT(column) - count non-null values in specific column
            let nonNullCount = values.filter { $0 != .null }.count
            return .count(nonNullCount)
        } else {
            // COUNT(*) - count all rows
            return .count(values.count)
        }
    }
    
    /// Executes SUM function
    private static func executeSum(_ values: [Value]) -> AggregateResult {
        let numericValues = values.compactMap { value -> Double? in
            switch value {
            case .int(let i): return Double(i)
            case .double(let d): return d
            case .decimal(let d): return Double(truncating: d as NSNumber)
            case .null: return nil
            default: return nil
            }
        }
        
        guard !numericValues.isEmpty else { return .null }
        let sum = numericValues.reduce(0, +)
        
        // Return as appropriate type
        if sum.truncatingRemainder(dividingBy: 1) == 0 {
            return .sum(.int(Int64(sum)))
        } else {
            return .sum(.double(sum))
        }
    }
    
    /// Executes AVG function
    private static func executeAvg(_ values: [Value]) -> AggregateResult {
        let numericValues = values.compactMap { value -> Double? in
            switch value {
            case .int(let i): return Double(i)
            case .double(let d): return d
            case .decimal(let d): return Double(truncating: d as NSNumber)
            case .null: return nil
            default: return nil
            }
        }
        
        guard !numericValues.isEmpty else { return .null }
        let avg = numericValues.reduce(0, +) / Double(numericValues.count)
        return .avg(avg)
    }
    
    /// Executes MIN function
    private static func executeMin(_ values: [Value]) -> AggregateResult {
        let nonNullValues = values.filter { $0 != .null }
        guard !nonNullValues.isEmpty else { return .null }
        
        // For numeric values, find minimum
        let numericValues = nonNullValues.compactMap { value -> Double? in
            switch value {
            case .int(let i): return Double(i)
            case .double(let d): return d
            case .decimal(let d): return Double(truncating: d as NSNumber)
            default: return nil
            }
        }
        
        if !numericValues.isEmpty {
            let minValue = numericValues.min()!
            if minValue.truncatingRemainder(dividingBy: 1) == 0 {
                return .min(.int(Int64(minValue)))
            } else {
                return .min(.double(minValue))
            }
        }
        
        // For string values, find lexicographically minimum
        let stringValues = nonNullValues.compactMap { value -> String? in
            switch value {
            case .string(let s): return s
            case .date(let d): return ISO8601DateFormatter().string(from: d)
            case .decimal(let d): return d.description
            default: return nil
            }
        }
        
        if !stringValues.isEmpty {
            return .min(.string(stringValues.min()!))
        }
        
        return .null
    }
    
    /// Executes MAX function
    private static func executeMax(_ values: [Value]) -> AggregateResult {
        let nonNullValues = values.filter { $0 != .null }
        guard !nonNullValues.isEmpty else { return .null }
        
        // For numeric values, find maximum
        let numericValues = nonNullValues.compactMap { value -> Double? in
            switch value {
            case .int(let i): return Double(i)
            case .double(let d): return d
            case .decimal(let d): return Double(truncating: d as NSNumber)
            default: return nil
            }
        }
        
        if !numericValues.isEmpty {
            let maxValue = numericValues.max()!
            if maxValue.truncatingRemainder(dividingBy: 1) == 0 {
                return .max(.int(Int64(maxValue)))
            } else {
                return .max(.double(maxValue))
            }
        }
        
        // For string values, find lexicographically maximum
        let stringValues = nonNullValues.compactMap { value -> String? in
            switch value {
            case .string(let s): return s
            case .date(let d): return ISO8601DateFormatter().string(from: d)
            case .decimal(let d): return d.description
            default: return nil
            }
        }
        
        if !stringValues.isEmpty {
            return .max(.string(stringValues.max()!))
        }
        
        return .null
    }
}

/// Built-in functions for data manipulation
public struct BuiltinFunctions {
    
    /// String functions
    public static func upper(_ value: Value) -> Value {
        switch value {
        case .string(let s): return .string(s.uppercased())
        default: return value
        }
    }
    
    public static func lower(_ value: Value) -> Value {
        switch value {
        case .string(let s): return .string(s.lowercased())
        default: return value
        }
    }
    
    public static func length(_ value: Value) -> Value {
        switch value {
        case .string(let s): return .int(Int64(s.count))
        default: return .null
        }
    }
    
    /// Date functions
    public static func now() -> Value {
        return .date(Date())
    }
    
    public static func year(_ value: Value) -> Value {
        switch value {
        case .date(let d):
            let calendar = Calendar.current
            let year = calendar.component(.year, from: d)
            return .int(Int64(year))
        default: return .null
        }
    }
    
    public static func month(_ value: Value) -> Value {
        switch value {
        case .date(let d):
            let calendar = Calendar.current
            let month = calendar.component(.month, from: d)
            return .int(Int64(month))
        default: return .null
        }
    }
    
    public static func day(_ value: Value) -> Value {
        switch value {
        case .date(let d):
            let calendar = Calendar.current
            let day = calendar.component(.day, from: d)
            return .int(Int64(day))
        default: return .null
        }
    }
    
    /// Numeric functions
    public static func abs(_ value: Value) -> Value {
        switch value {
        case .int(let i): return .int(i < 0 ? -i : i)
        case .double(let d): return .double(Swift.abs(d))
        case .decimal(let d): return .decimal(d.magnitude)
        default: return .null
        }
    }
    
    public static func roundValue(_ value: Value, to places: Int = 0) -> Value {
        switch value {
        case .double(let d):
            let multiplier = pow(10.0, Double(places))
            return .double(round(d * multiplier) / multiplier)
        case .decimal(let d):
            // Simple rounding for Decimal
            let doubleValue = Double(truncating: d as NSNumber)
            let multiplier = pow(10.0, Double(places))
            let rounded = Decimal(round(doubleValue * multiplier) / multiplier)
            return .decimal(rounded)
        default: return .null
        }
    }
    
    /// JSON functions
    public static func jsonExtract(_ value: Value, path: String) -> Value {
        // JSON functionality not implemented for MVP
        return .null
    }
    
    /// Helper to convert Any to Value
    private static func valueFromAny(_ any: Any) -> Value {
        if let string = any as? String { return .string(string) }
        if let int = any as? Int { return .int(Int64(int)) }
        if let double = any as? Double { return .double(double) }
        if let bool = any as? Bool { return .bool(bool) }
        // JSON types not supported in MVP
        return .null
    }
}
