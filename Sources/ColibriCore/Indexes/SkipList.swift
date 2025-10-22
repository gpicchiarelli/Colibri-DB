//
//  SkipList.swift
//  Based on: spec/SkipList.tla
//

import Foundation

// Use the Value type from Core/Types.swift
typealias Value = ColibriCore.Value

private class SkipListNode {
    let key: Value
    var rids: [RID]
    var forward: [SkipListNode?]
    
    init(key: Value, rids: [RID], level: Int) {
        self.key = key
        self.rids = rids
        self.forward = Array(repeating: nil, count: level)
    }
}

public actor SkipList {
    private let maxLevel = 16
    private let probability = 0.5
    private var head: SkipListNode
    private var level = 0
    
    public init() {
        self.head = SkipListNode(key: .null, rids: [], level: maxLevel)
    }
    
    private func randomLevel() -> Int {
        var lvl = 1
        while Double.random(in: 0...1) < probability && lvl < maxLevel {
            lvl += 1
        }
        return lvl
    }
    
    public func insert(key: Value, rid: RID) {
        var update = Array(repeating: head, count: maxLevel)
        var current: SkipListNode? = head
        
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < key {
                current = next
            }
            update[i] = current!
        }
        
        current = current?.forward[0]
        
        if let current = current, current.key == key {
            current.rids.append(rid)
        } else {
            let newLevel = randomLevel()
            
            if newLevel > level {
                for i in level..<newLevel {
                    update[i] = head
                }
                level = newLevel
            }
            
            let newNode = SkipListNode(key: key, rids: [rid], level: newLevel)
            
            for i in 0..<newLevel {
                newNode.forward[i] = update[i].forward[i]
                update[i].forward[i] = newNode
            }
        }
    }
    
    public func search(key: Value) -> [RID]? {
        var current: SkipListNode? = head
        
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < key {
                current = next
            }
        }
        
        current = current?.forward[0]
        
        if let current = current, current.key == key {
            return current.rids
        }
        
        return nil
    }
    
    public func rangeScan(minKey: Value, maxKey: Value) -> [(Value, [RID])] {
        var results: [(Value, [RID])] = []
        var current: SkipListNode? = head
        
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < minKey {
                current = next
            }
        }
        
        current = current?.forward[0]
        
        while let node = current, node.key <= maxKey {
            results.append((node.key, node.rids))
            current = node.forward[0]
        }
        
        return results
    }
}

