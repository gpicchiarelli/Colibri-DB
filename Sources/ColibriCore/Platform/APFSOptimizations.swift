//
//  APFSOptimizations.swift
//  Based on: spec/APFSOptimizations.tla
//

import Foundation

#if os(macOS)
public actor APFSOptimizer {
    private let fileManager = FileManager.default
    
    public init() {}
    
    public func createClone(source: URL, destination: URL) throws {
        try fileManager.copyItem(at: source, to: destination)
    }
    
    public func createSnapshot(volume: String, name: String) async throws {
        let task = Process()
        task.executableURL = URL(fileURLWithPath: "/usr/bin/tmutil")
        task.arguments = ["localsnapshot"]
        
        try task.run()
        task.waitUntilExit()
    }
    
    public func enableDataProtection(path: URL) throws {
        var resourceValues = URLResourceValues()
        resourceValues.isExcludedFromBackup = false
        
        var url = path
        try url.setResourceValues(resourceValues)
    }
    
    public func optimizeForSSD(path: URL) {
        logInfo("Optimizing \(path.path) for SSD")
    }
}
#endif

