//
//  Config.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Configuration atlas capturing runtime knobs and defaults.

import Foundation
/// Runtime configuration for ColibrìDB.
/// Provides sensible defaults and backward‑compatible decoding.

public struct DBConfig: Codable {
    public var dataDir: String
    public var maxConnectionsLogical: Int
    public var maxConnectionsPhysical: Int
    public var bufferPoolSizeBytes: UInt64
    public var pageSizeBytes: Int
    public var walEnabled: Bool
    public var checksumEnabled: Bool
    public var cliEnabled: Bool
    public var metricsEnabled: Bool
    public var serverEnabled: Bool
    public var indexImplementation: String // "Hash" | "BTree" | custom
    public var storageEngine: String // "FileHeap" | "InMemory"
    // Buffer pool parameters (defaults chosen for good dev experience)
    public var bufferPoolEnabled: Bool
    public var dataBufferPoolPages: Int   // number of pages in heap buffer pool
    public var indexBufferPoolPages: Int  // number of pages in index buffer pool
    // Online maintenance & compaction
    public var autoCompactionEnabled: Bool
    public var autoCompactionIntervalSeconds: Double
    public var autoCompactionPagesPerRun: Int
    public var heapFragmentationThreshold: Double
    public var heapFragmentationMinPages: Int
    public var heapFragmentationSamplePages: Int
    public var indexLeafOccupancyThreshold: Double
    public var indexCompactionCooldownSeconds: Double
    public var optimizerStatsSampleRows: Int
    public var lockTimeoutSeconds: Double
    public var defaultIsolationLevel: IsolationLevel
    public var walFullFSyncEnabled: Bool
    public var bufferFlushQoS: String
    public var ioSequentialReadHint: Bool
    public var walCompression: CompressionAlgorithm
    public var pageFlushCompression: CompressionAlgorithm
    public var walNoCache: Bool

    enum CodingKeys: String, CodingKey {
        case dataDir
        case maxConnectionsLogical
        case maxConnectionsPhysical
        case bufferPoolSizeBytes
        case pageSizeBytes
        case walEnabled
        case checksumEnabled
        case cliEnabled
        case metricsEnabled
        case serverEnabled
        case indexImplementation
        case storageEngine
        case bufferPoolEnabled
        case dataBufferPoolPages
        case indexBufferPoolPages
        case autoCompactionEnabled
        case autoCompactionIntervalSeconds
        case autoCompactionPagesPerRun
        case heapFragmentationThreshold
        case heapFragmentationMinPages
        case heapFragmentationSamplePages
        case indexLeafOccupancyThreshold
        case indexCompactionCooldownSeconds
        case optimizerStatsSampleRows
        case lockTimeoutSeconds
        case defaultIsolationLevel
        case walFullFSyncEnabled
        case bufferFlushQoS
        case ioSequentialReadHint
        case walCompression
        case pageFlushCompression
        case walNoCache
    }

    /// Initializes a configuration with defaults suited for development.
    public init(
        dataDir: String = "./data",
        maxConnectionsLogical: Int = 1_000_000,
        maxConnectionsPhysical: Int = 16,
        bufferPoolSizeBytes: UInt64 = 1 * 1024 * 1024 * 1024, // 1GB
        pageSizeBytes: Int = 8192,
        walEnabled: Bool = true,
        checksumEnabled: Bool = true,
        cliEnabled: Bool = true,
        metricsEnabled: Bool = true,
        serverEnabled: Bool = false,
        indexImplementation: String = "Hash",
        storageEngine: String = "FileHeap",
        bufferPoolEnabled: Bool = true,
        dataBufferPoolPages: Int = 16384,   // ~128MB @ 8KB
        indexBufferPoolPages: Int = 4096,   // ~32MB @ 8KB
        autoCompactionEnabled: Bool = true,
        autoCompactionIntervalSeconds: Double = 5.0,
        autoCompactionPagesPerRun: Int = 32,
        heapFragmentationThreshold: Double = 0.20,
        heapFragmentationMinPages: Int = 8,
        heapFragmentationSamplePages: Int = 32,
        indexLeafOccupancyThreshold: Double = 0.60,
        indexCompactionCooldownSeconds: Double = 30.0,
        optimizerStatsSampleRows: Int = 1024,
        lockTimeoutSeconds: Double = 5.0,
        defaultIsolationLevel: IsolationLevel = .readCommitted,
        walFullFSyncEnabled: Bool = false,
        bufferFlushQoS: String = "utility",
        ioSequentialReadHint: Bool = false,
        walCompression: CompressionAlgorithm = .none,
        pageFlushCompression: CompressionAlgorithm = .none,
        walNoCache: Bool = false
    ) {
        self.dataDir = dataDir
        self.maxConnectionsLogical = maxConnectionsLogical
        self.maxConnectionsPhysical = maxConnectionsPhysical
        self.bufferPoolSizeBytes = bufferPoolSizeBytes
        self.pageSizeBytes = pageSizeBytes
        self.walEnabled = walEnabled
        self.checksumEnabled = checksumEnabled
        self.cliEnabled = cliEnabled
        self.metricsEnabled = metricsEnabled
        self.serverEnabled = serverEnabled
        self.indexImplementation = indexImplementation
        self.storageEngine = storageEngine
        self.bufferPoolEnabled = bufferPoolEnabled
        self.dataBufferPoolPages = dataBufferPoolPages
        self.indexBufferPoolPages = indexBufferPoolPages
        self.autoCompactionEnabled = autoCompactionEnabled
        self.autoCompactionIntervalSeconds = autoCompactionIntervalSeconds
        self.autoCompactionPagesPerRun = autoCompactionPagesPerRun
        self.heapFragmentationThreshold = heapFragmentationThreshold
        self.heapFragmentationMinPages = heapFragmentationMinPages
        self.heapFragmentationSamplePages = heapFragmentationSamplePages
        self.indexLeafOccupancyThreshold = indexLeafOccupancyThreshold
        self.indexCompactionCooldownSeconds = indexCompactionCooldownSeconds
        self.optimizerStatsSampleRows = optimizerStatsSampleRows
        self.lockTimeoutSeconds = lockTimeoutSeconds
        self.defaultIsolationLevel = defaultIsolationLevel
        self.walFullFSyncEnabled = walFullFSyncEnabled
        self.bufferFlushQoS = bufferFlushQoS
        self.ioSequentialReadHint = ioSequentialReadHint
        self.walCompression = walCompression
        self.pageFlushCompression = pageFlushCompression
        self.walNoCache = walNoCache
    }

    // Backward-compatible decoding: missing keys fall back to defaults
    /// Backward‑compatible decoding: missing keys fall back to defaults.
    public init(from decoder: Decoder) throws {
        let d = DBConfig() // defaults
        let c = try decoder.container(keyedBy: CodingKeys.self)
        self.dataDir = try c.decodeIfPresent(String.self, forKey: .dataDir) ?? d.dataDir
        self.maxConnectionsLogical = try c.decodeIfPresent(Int.self, forKey: .maxConnectionsLogical) ?? d.maxConnectionsLogical
        self.maxConnectionsPhysical = try c.decodeIfPresent(Int.self, forKey: .maxConnectionsPhysical) ?? d.maxConnectionsPhysical
        self.bufferPoolSizeBytes = try c.decodeIfPresent(UInt64.self, forKey: .bufferPoolSizeBytes) ?? d.bufferPoolSizeBytes
        self.pageSizeBytes = try c.decodeIfPresent(Int.self, forKey: .pageSizeBytes) ?? d.pageSizeBytes
        self.walEnabled = try c.decodeIfPresent(Bool.self, forKey: .walEnabled) ?? d.walEnabled
        self.checksumEnabled = try c.decodeIfPresent(Bool.self, forKey: .checksumEnabled) ?? d.checksumEnabled
        self.cliEnabled = try c.decodeIfPresent(Bool.self, forKey: .cliEnabled) ?? d.cliEnabled
        self.metricsEnabled = try c.decodeIfPresent(Bool.self, forKey: .metricsEnabled) ?? d.metricsEnabled
        self.serverEnabled = try c.decodeIfPresent(Bool.self, forKey: .serverEnabled) ?? d.serverEnabled
        self.indexImplementation = try c.decodeIfPresent(String.self, forKey: .indexImplementation) ?? d.indexImplementation
        self.storageEngine = try c.decodeIfPresent(String.self, forKey: .storageEngine) ?? d.storageEngine
        self.bufferPoolEnabled = try c.decodeIfPresent(Bool.self, forKey: .bufferPoolEnabled) ?? d.bufferPoolEnabled
        self.dataBufferPoolPages = try c.decodeIfPresent(Int.self, forKey: .dataBufferPoolPages) ?? d.dataBufferPoolPages
        self.indexBufferPoolPages = try c.decodeIfPresent(Int.self, forKey: .indexBufferPoolPages) ?? d.indexBufferPoolPages
        self.autoCompactionEnabled = try c.decodeIfPresent(Bool.self, forKey: .autoCompactionEnabled) ?? d.autoCompactionEnabled
        self.autoCompactionIntervalSeconds = try c.decodeIfPresent(Double.self, forKey: .autoCompactionIntervalSeconds) ?? d.autoCompactionIntervalSeconds
        self.autoCompactionPagesPerRun = try c.decodeIfPresent(Int.self, forKey: .autoCompactionPagesPerRun) ?? d.autoCompactionPagesPerRun
        self.heapFragmentationThreshold = try c.decodeIfPresent(Double.self, forKey: .heapFragmentationThreshold) ?? d.heapFragmentationThreshold
        self.heapFragmentationMinPages = try c.decodeIfPresent(Int.self, forKey: .heapFragmentationMinPages) ?? d.heapFragmentationMinPages
        self.heapFragmentationSamplePages = try c.decodeIfPresent(Int.self, forKey: .heapFragmentationSamplePages) ?? d.heapFragmentationSamplePages
        self.indexLeafOccupancyThreshold = try c.decodeIfPresent(Double.self, forKey: .indexLeafOccupancyThreshold) ?? d.indexLeafOccupancyThreshold
        self.indexCompactionCooldownSeconds = try c.decodeIfPresent(Double.self, forKey: .indexCompactionCooldownSeconds) ?? d.indexCompactionCooldownSeconds
        self.optimizerStatsSampleRows = try c.decodeIfPresent(Int.self, forKey: .optimizerStatsSampleRows) ?? d.optimizerStatsSampleRows
        self.lockTimeoutSeconds = try c.decodeIfPresent(Double.self, forKey: .lockTimeoutSeconds) ?? d.lockTimeoutSeconds
        self.defaultIsolationLevel = try c.decodeIfPresent(IsolationLevel.self, forKey: .defaultIsolationLevel) ?? d.defaultIsolationLevel
        self.walFullFSyncEnabled = try c.decodeIfPresent(Bool.self, forKey: .walFullFSyncEnabled) ?? d.walFullFSyncEnabled
        self.bufferFlushQoS = try c.decodeIfPresent(String.self, forKey: .bufferFlushQoS) ?? d.bufferFlushQoS
        self.ioSequentialReadHint = try c.decodeIfPresent(Bool.self, forKey: .ioSequentialReadHint) ?? d.ioSequentialReadHint
        self.walCompression = try c.decodeIfPresent(CompressionAlgorithm.self, forKey: .walCompression) ?? d.walCompression
        self.pageFlushCompression = try c.decodeIfPresent(CompressionAlgorithm.self, forKey: .pageFlushCompression) ?? d.pageFlushCompression
        self.walNoCache = try c.decodeIfPresent(Bool.self, forKey: .walNoCache) ?? d.walNoCache
    }
}

/// Helpers to load/save DBConfig from/to JSON files.
public enum ConfigIO {
    /// Loads configuration from a JSON file, returning defaults if file is missing.
    /// - Parameter path: Optional path (defaults to `colibridb.conf.json`).
    /// - Throws: `DBError.config` on parse errors.
    public static func load(from path: String?) throws -> DBConfig {
        let fm = FileManager.default
        let resolved = path ?? "colibridb.conf.json"
        if !fm.fileExists(atPath: resolved) {
            // Return defaults if not found
            return DBConfig()
        }
        let url = URL(fileURLWithPath: resolved)
        let data = try Data(contentsOf: url)
        do {
            return try JSONDecoder().decode(DBConfig.self, from: data)
        } catch {
            throw DBError.config("Failed to parse config JSON at \(resolved): \(error)")
        }
    }

    /// Saves configuration to a JSON file.
    /// - Parameters:
    ///   - cfg: Configuration object.
    ///   - path: Optional path (defaults to `colibridb.conf.json`).
    public static func save(_ cfg: DBConfig, to path: String? = nil) throws {
        let resolved = path ?? "colibridb.conf.json"
        let url = URL(fileURLWithPath: resolved)
        let data = try JSONEncoder().encode(cfg)
        try data.write(to: url)
    }
}
