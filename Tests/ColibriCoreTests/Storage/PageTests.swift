//
//  PageTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Page Tests")
struct PageTests {
    
    @Test("Create empty page")
    func testCreateEmptyPage() {
        let page = Page(pageId: 1, pageSize: 8192)
        
        #expect(page.pageId == 1)
        #expect(page.slotCount() == 0)
    }
    
    @Test("Insert slot into page")
    func testInsertSlot() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        let data = Data("test data".utf8)
        
        let slotId = try page.insertSlot(data)
        
        #expect(slotId >= 0)
        #expect(page.slotCount() == 1)
    }
    
    @Test("Read slot from page")
    func testReadSlot() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        let data = Data("test data".utf8)
        
        let slotId = try page.insertSlot(data)
        let retrieved = try page.readSlot(slotId)
        
        #expect(retrieved == data)
    }
    
    @Test("Update slot in page")
    func testUpdateSlot() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        let originalData = Data("original".utf8)
        
        let slotId = try page.insertSlot(originalData)
        
        let newData = Data("updated".utf8)
        try page.updateSlot(slotId, newData)
        
        let retrieved = try page.readSlot(slotId)
        #expect(retrieved == newData)
    }
    
    @Test("Delete slot from page")
    func testDeleteSlot() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        let data = Data("test".utf8)
        
        let slotId = try page.insertSlot(data)
        try page.deleteSlot(slotId)
        
        #expect(throws: Error.self) {
            _ = try page.readSlot(slotId)
        }
    }
    
    @Test("Page serialization roundtrip")
    func testSerialization() throws {
        var page = Page(pageId: 42, pageSize: 8192)
        _ = try page.insertSlot(Data("data1".utf8))
        _ = try page.insertSlot(Data("data2".utf8))
        
        let serialized = try page.serialize()
        let deserialized = try Page.deserialize(serialized, pageSize: 8192)
        
        #expect(deserialized.pageId == 42)
        #expect(deserialized.slotCount() == 2)
    }
    
    @Test("Page available space tracking")
    func testAvailableSpace() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        let initialSpace = page.availableSpaceForInsert()
        
        let data = Data(repeating: 0, count: 1000)
        _ = try page.insertSlot(data)
        
        let remainingSpace = page.availableSpaceForInsert()
        #expect(remainingSpace < initialSpace)
    }
    
    @Test("Page fills up correctly")
    func testPageFillup() throws {
        var page = Page(pageId: 1, pageSize: 8192)
        var insertCount = 0
        
        let largeData = Data(repeating: 0, count: 500)
        
        while page.availableSpaceForInsert() > 600 {
            _ = try page.insertSlot(largeData)
            insertCount += 1
        }
        
        #expect(insertCount > 0)
        #expect(page.availableSpaceForInsert() < 600)
    }
}

