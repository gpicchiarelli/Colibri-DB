//
//  StatisticsMaintenance.swift
//  Based on: spec/StatisticsMaintenance.tla
//

import Foundation

public struct ColumnStatistics {
    public let columnName: String
    public let distinctCount: Int
    public let nullCount: Int
    public let minValue: Value?
    public let maxValue: Value?
    public let avgSize: Int
    
    public init(columnName: String, distinctCount: Int, nullCount: Int, minValue: Value?, maxValue: Value?, avgSize: Int) {
        self.columnName = columnName
        self.distinctCount = distinctCount
        self.nullCount = nullCount
        self.minValue = minValue
        self.maxValue = maxValue
        self.avgSize = avgSize
    }
}

public actor StatisticsMaintenanceManager {
    private var tableStatistics: [String: TableStatistics] = [:]
    private var columnStatistics: [String: [String: ColumnStatistics]] = [:]
    private var lastAnalyzed: [String: Date] = [:]
    
    public init() {}
    
    public func analyze(table: String, rows: [Row]) async {
        let rowCount = rows.count
        let pageCount = (rowCount / 100) + 1
        let avgRowSize = rows.isEmpty ? 0 : rows[0].values.reduce(0) { sum, value in
            sum + estimateSize(value)
        }
        
        tableStatistics[table] = TableStatistics(
            pageCount: pageCount,
            rowCount: rowCount,
            avgRowSize: avgRowSize
        )
        
        if let firstRow = rows.first {
            var colStats: [String: ColumnStatistics] = [:]
            
            for (columnName, _) in firstRow {
                let values = rows.compactMap { $0[columnName] }
                let nullCount = rows.count - values.count
                let distinctCount = Set(values.map { "\($0)" }).count
                let minValue = values.min { a, b in compareValues(a, b) < 0 }
                let maxValue = values.max { a, b in compareValues(a, b) < 0 }
                let avgSize = values.reduce(0) { $0 + estimateSize($1) } / max(1, values.count)
                
                colStats[columnName] = ColumnStatistics(
                    columnName: columnName,
                    distinctCount: distinctCount,
                    nullCount: nullCount,
                    minValue: minValue,
                    maxValue: maxValue,
                    avgSize: avgSize
                )
            }
            
            columnStatistics[table] = colStats
        }
        
        lastAnalyzed[table] = Date()
    }
    
    public func getTableStatistics(_ table: String) -> TableStatistics? {
        return tableStatistics[table]
    }
    
    public func getColumnStatistics(_ table: String, column: String) -> ColumnStatistics? {
        return columnStatistics[table]?[column]
    }
    
    public func shouldAnalyze(_ table: String) -> Bool {
        guard let lastTime = lastAnalyzed[table] else {
            return true
        }
        
        return Date().timeIntervalSince(lastTime) > 86400
    }
    
    private func estimateSize(_ value: Value) -> Int {
        switch value {
        case .int: return 8
        case .double: return 8
        case .bool: return 1
        case .string(let s): return s.utf8.count
        case .null: return 0
        case .decimal: return 16
        case .date: return 8
        case .bytes(let d): return d.count
        }
    }
    
    private func compareValues(_ a: Value, _ b: Value) -> Int {
        switch (a, b) {
        case (.int(let x), .int(let y)): return x < y ? -1 : (x > y ? 1 : 0)
        case (.double(let x), .double(let y)): return x < y ? -1 : (x > y ? 1 : 0)
        case (.string(let x), .string(let y)): return x < y ? -1 : (x > y ? 1 : 0)
        default: return 0
        }
    }
}

