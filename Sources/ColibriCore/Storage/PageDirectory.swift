//
//  PageDirectory.swift
//  ColibrìDB
//
//  Tracks heap page metadata (free space, checksum, last LSN) and persists it to disk
//  so that heap management follows the ARIES model (Gray & Reuter, 1993).
//

import Foundation

/// Metadata for a single heap page.
public struct PageInfo: Codable, Sendable {
    public let pageID: PageID
    public var freeBytes: Int
    public var checksum: UInt32
    public var lastLSN: LSN
    
    public init(pageID: PageID, freeBytes: Int, checksum: UInt32, lastLSN: LSN) {
        self.pageID = pageID
        self.freeBytes = freeBytes
        self.checksum = checksum
        self.lastLSN = lastLSN
    }
}

/// Persistent directory for heap pages.
public actor PageDirectory {
    private var pages: [PageID: PageInfo]
    private let fileURL: URL
    private let inMemory: Bool
    private let encoder = JSONEncoder()
    private let decoder = JSONDecoder()
    
    public init(fileURL: URL, inMemory: Bool = false) throws {
        self.fileURL = fileURL
        self.inMemory = inMemory
        if inMemory || !FileManager.default.fileExists(atPath: fileURL.path) {
            self.pages = [:]
        } else {
            let data = try Data(contentsOf: fileURL)
            self.pages = try decoder.decode([PageID: PageInfo].self, from: data)
        }
    }
    
    public func registerPage(pageID: PageID, freeBytes: Int, checksum: UInt32, lsn: LSN) async throws {
        pages[pageID] = PageInfo(pageID: pageID, freeBytes: freeBytes, checksum: checksum, lastLSN: lsn)
        try persist()
    }
    
    public func updatePage(pageID: PageID, freeBytes: Int, checksum: UInt32, lsn: LSN) async throws {
        guard var info = pages[pageID] else { return }
        info.freeBytes = freeBytes
        info.checksum = checksum
        info.lastLSN = max(info.lastLSN, lsn)
        pages[pageID] = info
        try persist()
    }
    
    public func removePage(pageID: PageID) async throws {
        pages.removeValue(forKey: pageID)
        try persist()
    }
    
    public func page(withFreeSpace requiredBytes: Int) -> PageID? {
        return pages
            .values
            .filter { $0.freeBytes >= requiredBytes }
            .sorted { $0.freeBytes < $1.freeBytes }
            .first?
            .pageID
    }
    
    public func allPageIDs() -> [PageID] {
        return Array(pages.keys).sorted()
    }
    
    public func nextAvailablePageID() -> PageID {
        return (pages.keys.max() ?? 0) + 1
    }
    
    public func pageInfo(pageID: PageID) -> PageInfo? {
        return pages[pageID]
    }
    
    private func persist() throws {
        guard !inMemory else { return }
        let data = try encoder.encode(pages)
        try FileManager.default.createDirectory(
            at: fileURL.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        try data.write(to: fileURL, options: .atomic)
    }
}

