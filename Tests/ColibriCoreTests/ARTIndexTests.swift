//
//  ARTIndexTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: ART chronicles exploring adaptive radix behavior.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct ARTIndexTests {
    @Test func pathCompressionSurvivesInsertSearchAndRemove() throws {
        let index = ARTIndex<Int>()
        try index.insert("car", 1)
        try index.insert("card", 2)
        try index.insert("cart", 3)
        try index.insert("dog", 4)

        let carMatches = try index.searchEquals("car")
        #expect(Set(carMatches) == [1])

        let rangeMatches = try index.range("car", "caz")
        #expect(Set(rangeMatches) == [1, 2, 3])

        try index.remove("card", 2)
        let rangeAfterDelete = try index.range("car", "caz")
        #expect(Set(rangeAfterDelete) == [1, 3])

        // Removing a non-existing key/reference pair is a no-op.
        try index.remove("card", 2)
        #expect(try index.searchEquals("card").isEmpty)
    }

    @Test func pruningCollapsesDanglingBranches() throws {
        let index = ARTIndex<Int>()
        try index.insert("apple", 10)
        try index.insert("application", 11)
        try index.insert("apricot", 12)

        try index.remove("application", 11)
        #expect(Set(try index.searchEquals("apple")) == [10])

        try index.remove("apple", 10)
        #expect(try index.searchEquals("apple").isEmpty)

        let remaining = try index.range("ap", "apz")
        #expect(Set(remaining) == [12])
    }

    @Test func tombstoneFlowSkipsDeletesUntilCompaction() throws {
        let index = ARTIndex<RID>()
        let rid = RID(pageId: 1, slotId: 1)

        try index.insert("ghost", rid)
        try index.remove("ghost", rid)

        // Tombstone keeps entry invisible
        #expect(try index.searchEquals("ghost").isEmpty)

        // Reinserting same RID resurrects visibility
        try index.insert("ghost", rid)
        let hits = try index.searchEquals("ghost")
        #expect(hits == [rid])
    }
}

