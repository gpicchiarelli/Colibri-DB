//
//  JoinAlgorithms.swift
//  Based on: spec/JoinAlgorithms.tla
//

import Foundation

public enum JoinType {
    case inner
    case leftOuter
    case rightOuter
    case fullOuter
    case cross
}

public actor JoinExecutor {
    public init() {}
    
    public func nestedLoopJoin(
        left: [Row],
        right: [Row],
        predicate: (Row, Row) -> Bool,
        type: JoinType = .inner
    ) -> [Row] {
        var results: [Row] = []
        
        for leftRow in left {
            var matched = false
            
            for rightRow in right {
                if predicate(leftRow, rightRow) {
                    var merged = leftRow
                    for (key, value) in rightRow {
                        merged[key] = value
                    }
                    results.append(merged)
                    matched = true
                }
            }
            
            if !matched && (type == .leftOuter || type == .fullOuter) {
                results.append(leftRow)
            }
        }
        
        if type == .rightOuter || type == .fullOuter {
            for rightRow in right {
                let matched = left.contains { leftRow in
                    predicate(leftRow, rightRow)
                }
                
                if !matched {
                    results.append(rightRow)
                }
            }
        }
        
        return results
    }
    
    public func hashJoin(
        left: [Row],
        right: [Row],
        leftKey: String,
        rightKey: String
    ) -> [Row] {
        var hashTable: [String: [Row]] = [:]
        
        for row in left {
            let key = "\(row[leftKey] ?? .null)"
            hashTable[key, default: []].append(row)
        }
        
        var results: [Row] = []
        
        for rightRow in right {
            let key = "\(rightRow[rightKey] ?? .null)"
            
            if let matchingRows = hashTable[key] {
                for leftRow in matchingRows {
                    var merged = leftRow
                    for (k, v) in rightRow {
                        merged[k] = v
                    }
                    results.append(merged)
                }
            }
        }
        
        return results
    }
    
    public func sortMergeJoin(
        left: [Row],
        right: [Row],
        leftKey: String,
        rightKey: String
    ) -> [Row] {
        let sortedLeft = left.sorted { r1, r2 in
            let v1 = "\(r1[leftKey] ?? .null)"
            let v2 = "\(r2[leftKey] ?? .null)"
            return v1 < v2
        }
        
        let sortedRight = right.sorted { r1, r2 in
            let v1 = "\(r1[rightKey] ?? .null)"
            let v2 = "\(r2[rightKey] ?? .null)"
            return v1 < v2
        }
        
        var results: [Row] = []
        var i = 0
        var j = 0
        
        while i < sortedLeft.count && j < sortedRight.count {
            let leftVal = "\(sortedLeft[i][leftKey] ?? .null)"
            let rightVal = "\(sortedRight[j][rightKey] ?? .null)"
            
            if leftVal < rightVal {
                i += 1
            } else if leftVal > rightVal {
                j += 1
            } else {
                var merged = sortedLeft[i]
                for (k, v) in sortedRight[j] {
                    merged[k] = v
                }
                results.append(merged)
                j += 1
            }
        }
        
        return results
    }
}

