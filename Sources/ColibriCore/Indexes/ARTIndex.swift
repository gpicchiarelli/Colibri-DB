//
//  ARTIndex.swift
//  Adaptive Radix Tree Index
//  Based on: spec/ARTIndex.tla
//

import Foundation

private class ARTNode {
    var children: [UInt8: ARTNode] = [:]
    var value: [RID]?
    var prefix: [UInt8] = []
    
    func addChild(byte: UInt8, node: ARTNode) {
        children[byte] = node
    }
    
    func getChild(byte: UInt8) -> ARTNode? {
        return children[byte]
    }
}

public actor ARTIndex {
    private var root: ARTNode = ARTNode()
    
    public init() {}
    
    public func insert(key: Data, rid: RID) {
        var current = root
        
        for byte in key {
            if let child = current.getChild(byte: byte) {
                current = child
            } else {
                let newNode = ARTNode()
                current.addChild(byte: byte, node: newNode)
                current = newNode
            }
        }
        
        if current.value != nil {
            current.value?.append(rid)
        } else {
            current.value = [rid]
        }
    }
    
    public func search(key: Data) -> [RID]? {
        var current = root
        
        for byte in key {
            guard let child = current.getChild(byte: byte) else {
                return nil
            }
            current = child
        }
        
        return current.value
    }
    
    public func prefixScan(prefix: Data) -> [(Data, [RID])] {
        var results: [(Data, [RID])] = []
        var current = root
        
        for byte in prefix {
            guard let child = current.getChild(byte: byte) else {
                return results
            }
            current = child
        }
        
        collectAll(node: current, prefix: prefix, results: &results)
        return results
    }
    
    private func collectAll(node: ARTNode, prefix: Data, results: inout [(Data, [RID])]) {
        if let value = node.value {
            results.append((prefix, value))
        }
        
        for (byte, child) in node.children {
            var newPrefix = prefix
            newPrefix.append(byte)
            collectAll(node: child, prefix: newPrefix, results: &results)
        }
    }
}

