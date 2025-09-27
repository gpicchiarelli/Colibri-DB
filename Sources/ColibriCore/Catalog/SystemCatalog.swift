//
//  SystemCatalog.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: System catalog archive recording objects, roles, and stats.

import Foundation

/// Persistent catalog that tracks logical (tables, indexes, views, sequences) and physical
/// objects (heap files, index files, segments) for ColibrìDB.
public final class SystemCatalog {
    public enum LogicalKind: String, Codable, Sendable { case table, index, view, sequence }
    public enum PhysicalKind: String, Codable, Sendable { case heapFile, indexFile, segment, other }
    public enum RoleKind: String, Codable, Sendable { case user, group }
    public enum StatisticKind: String, Codable { case table, column }

    public struct LogicalObject: Codable, Identifiable {
        public var id: UUID
        public var name: String
        public var schema: String?
        public var kind: LogicalKind
        public var parentName: String?
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    public struct PhysicalObject: Codable, Identifiable {
        public var id: UUID
        public var logicalId: UUID?
        public var kind: PhysicalKind
        public var path: String?
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    public struct RoleEntry: Codable, Identifiable {
        public var id: UUID
        public var name: String
        public var kind: RoleKind
        public var members: [String]
        public var privileges: [String]
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    public struct StatisticEntry: Codable, Identifiable {
        public var id: UUID
        public var table: String
        public var column: String?
        public var kind: StatisticKind
        public var stats: [String: Double]
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    public struct ConfigurationEntry: Codable, Identifiable {
        public var id: UUID
        public var scope: String
        public var key: String
        public var value: String
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    public struct StructurePreference: Codable, Identifiable {
        public var id: UUID
        public var table: String
        public var columns: [String]
        public var structure: String
        public var metadata: [String: String]
        public var createdAt: Date
        public var updatedAt: Date
    }

    private struct Snapshot: Codable {
        var logical: [LogicalObject]
        var physical: [PhysicalObject]
        var roles: [RoleEntry]
        var statistics: [StatisticEntry]
        var configurations: [ConfigurationEntry]
        var structures: [StructurePreference]
    }

    private let fileURL: URL
    private let queue = DispatchQueue(label: "ColibriDB.SystemCatalog", attributes: .concurrent)
    private var snapshot: Snapshot
    private let encoder: JSONEncoder = {
        let enc = JSONEncoder()
        enc.outputFormatting = [.prettyPrinted, .sortedKeys]
        return enc
    }()
    private let decoder = JSONDecoder()

    public init(path: String) throws {
        self.fileURL = URL(fileURLWithPath: path)
        let fm = FileManager.default
        let dir = fileURL.deletingLastPathComponent()
        try fm.createDirectory(at: dir, withIntermediateDirectories: true)
        if fm.fileExists(atPath: path) {
            do {
                let data = try Data(contentsOf: fileURL)
                snapshot = try decoder.decode(Snapshot.self, from: data)
            } catch {
                snapshot = Snapshot(logical: [], physical: [], roles: [], statistics: [], configurations: [], structures: [])
            }
        } else {
            snapshot = Snapshot(logical: [], physical: [], roles: [], statistics: [], configurations: [], structures: [])
            try persistLocked()
        }
    }

    // MARK: - Public API
    @discardableResult
    public func registerTable(name: String, schema: String? = nil, storage: String, physicalPath: String?, pageSize: Int?, inMemory: Bool) -> LogicalObject {
        queue.sync(flags: .barrier) {
            let now = Date()
            let key = { (obj: LogicalObject) -> Bool in
                obj.kind == .table && obj.name == name && obj.schema == schema
            }
            if let idx = snapshot.logical.firstIndex(where: key) {
                snapshot.logical[idx].metadata = mergedMetadata(snapshot.logical[idx].metadata, ["storage": storage, "pageSize": stringOpt(pageSize), "inMemory": String(inMemory)])
                snapshot.logical[idx].updatedAt = now
                if let path = physicalPath {
                    upsertPhysicalLocked(logicalId: snapshot.logical[idx].id, kind: .heapFile, path: path, pageSize: pageSize, sizeBytes: fileSize(path: path))
                }
                try? persistLocked()
                return snapshot.logical[idx]
            }
            var metadata: [String: String] = ["storage": storage, "inMemory": String(inMemory)]
            if let pageSize = pageSize { metadata["pageSize"] = String(pageSize) }
            let logical = LogicalObject(id: UUID(), name: name, schema: schema, kind: .table, parentName: nil, metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.logical.append(logical)
            if let path = physicalPath {
                upsertPhysicalLocked(logicalId: logical.id, kind: .heapFile, path: path, pageSize: pageSize, sizeBytes: fileSize(path: path))
            }
            try? persistLocked()
            return logical
        }
    }

    @discardableResult
    public func registerIndex(name: String, table: String, kind: String, physicalPath: String?, columns: [String]) -> LogicalObject {
        queue.sync(flags: .barrier) {
            let now = Date()
            let key = { (obj: LogicalObject) -> Bool in
                obj.kind == .index && obj.name == name && obj.parentName == table
            }
            let metadata: [String: String] = ["indexKind": kind.lowercased(), "table": table, "columns": columns.joined(separator: ",")]
            if let idx = snapshot.logical.firstIndex(where: key) {
                snapshot.logical[idx].metadata = mergedMetadata(snapshot.logical[idx].metadata, metadata)
                snapshot.logical[idx].updatedAt = now
                if let path = physicalPath {
                    upsertPhysicalLocked(logicalId: snapshot.logical[idx].id, kind: .indexFile, path: path, pageSize: nil, sizeBytes: fileSize(path: path))
                }
                try? persistLocked()
                return snapshot.logical[idx]
            }
            let logical = LogicalObject(id: UUID(), name: name, schema: nil, kind: .index, parentName: table, metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.logical.append(logical)
            if let path = physicalPath {
                upsertPhysicalLocked(logicalId: logical.id, kind: .indexFile, path: path, pageSize: nil, sizeBytes: fileSize(path: path))
            }
            try? persistLocked()
            return logical
        }
    }

    public func removeIndex(name: String, table: String) {
        queue.sync(flags: .barrier) {
            let ids = snapshot.logical.filter { $0.kind == .index && $0.name == name && $0.parentName == table }.map { $0.id }
            if ids.isEmpty { return }
            snapshot.logical.removeAll { ids.contains($0.id) }
            snapshot.physical.removeAll { obj in
                guard let logicalId = obj.logicalId else { return false }
                return ids.contains(logicalId)
            }
            snapshot.structures.removeAll { $0.table == table && $0.metadata["index"] == name }
            try? persistLocked()
        }
    }

    @discardableResult
    public func registerRole(name: String, kind: RoleKind, members: [String] = [], privileges: [String] = [], metadata: [String: String] = [:]) -> RoleEntry {
        queue.sync(flags: .barrier) {
            let now = Date()
            if let idx = snapshot.roles.firstIndex(where: { $0.name == name && $0.kind == kind }) {
                var entry = snapshot.roles[idx]
                entry.members = Array(Set(entry.members).union(members))
                entry.privileges = Array(Set(entry.privileges).union(privileges))
                entry.metadata = mergedMetadata(entry.metadata, metadata)
                entry.updatedAt = now
                snapshot.roles[idx] = entry
                try? persistLocked()
                return entry
            }
            let entry = RoleEntry(id: UUID(), name: name, kind: kind, members: Array(Set(members)), privileges: Array(Set(privileges)), metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.roles.append(entry)
            try? persistLocked()
            return entry
        }
    }

    public func addRoleMembership(name: String, kind: RoleKind, member: String) {
        queue.sync(flags: .barrier) {
            guard let idx = snapshot.roles.firstIndex(where: { $0.name == name && $0.kind == kind }) else { return }
            if !snapshot.roles[idx].members.contains(member) {
                snapshot.roles[idx].members.append(member)
                snapshot.roles[idx].updatedAt = Date()
                try? persistLocked()
            }
        }
    }

    public func setRolePrivileges(name: String, kind: RoleKind, privileges: [String]) {
        queue.sync(flags: .barrier) {
            guard let idx = snapshot.roles.firstIndex(where: { $0.name == name && $0.kind == kind }) else { return }
            snapshot.roles[idx].privileges = Array(Set(privileges))
            snapshot.roles[idx].updatedAt = Date()
            try? persistLocked()
        }
    }

    @discardableResult
    public func registerStatistic(table: String, column: String?, stats: [String: Double], metadata: [String: String] = [:]) -> StatisticEntry {
        queue.sync(flags: .barrier) {
            let now = Date()
            if let idx = snapshot.statistics.firstIndex(where: { $0.table == table && $0.column == column }) {
                var entry = snapshot.statistics[idx]
                entry.stats = stats
                entry.metadata = mergedMetadata(entry.metadata, metadata)
                entry.updatedAt = now
                snapshot.statistics[idx] = entry
                try? persistLocked()
                return entry
            }
            let entry = StatisticEntry(id: UUID(), table: table, column: column, kind: column == nil ? .table : .column, stats: stats, metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.statistics.append(entry)
            try? persistLocked()
            return entry
        }
    }

    @discardableResult
    public func registerConfiguration(scope: String, key: String, value: String, metadata: [String: String] = [:]) -> ConfigurationEntry {
        queue.sync(flags: .barrier) {
            let now = Date()
            if let idx = snapshot.configurations.firstIndex(where: { $0.scope == scope && $0.key == key }) {
                var entry = snapshot.configurations[idx]
                entry.value = value
                entry.metadata = mergedMetadata(entry.metadata, metadata)
                entry.updatedAt = now
                snapshot.configurations[idx] = entry
                try? persistLocked()
                return entry
            }
            let entry = ConfigurationEntry(id: UUID(), scope: scope, key: key, value: value, metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.configurations.append(entry)
            try? persistLocked()
            return entry
        }
    }

    @discardableResult
    public func registerStructurePreference(table: String, columns: [String], structure: String, metadata: [String: String] = [:]) -> StructurePreference {
        queue.sync(flags: .barrier) {
            let canonicalColumns = columns.map { $0.lowercased() }.sorted()
            let now = Date()
            if let idx = snapshot.structures.firstIndex(where: { $0.table == table && $0.columns == canonicalColumns }) {
                var entry = snapshot.structures[idx]
                entry.structure = structure
                entry.metadata = mergedMetadata(entry.metadata, metadata)
                entry.updatedAt = now
                snapshot.structures[idx] = entry
                try? persistLocked()
                return entry
            }
            let entry = StructurePreference(id: UUID(), table: table, columns: canonicalColumns, structure: structure, metadata: metadata, createdAt: now, updatedAt: now)
            snapshot.structures.append(entry)
            try? persistLocked()
            return entry
        }
    }

    public func logicalObjects(kind: LogicalKind? = nil) -> [LogicalObject] {
        queue.sync {
            guard let kind = kind else { return snapshot.logical }
            return snapshot.logical.filter { $0.kind == kind }
        }
    }

    // MARK: - Convenience removals
    public func removeLogical(name: String, kind: LogicalKind) {
        queue.async(flags: .barrier) { @Sendable [weak self, kind] in
            guard let self = self else { return }
            self.snapshot.logical.removeAll { $0.name == name && $0.kind == kind }
            try? self.persistLocked()
        }
    }

    public func physicalObjects(kind: PhysicalKind? = nil) -> [PhysicalObject] {
        queue.sync {
            guard let kind = kind else { return snapshot.physical }
            return snapshot.physical.filter { $0.kind == kind }
        }
    }

    public func roles(kind: RoleKind? = nil) -> [RoleEntry] {
        queue.sync {
            guard let kind = kind else { return snapshot.roles }
            return snapshot.roles.filter { $0.kind == kind }
        }
    }

    public func statistics(table: String? = nil, column: String? = nil) -> [StatisticEntry] {
        queue.sync {
            snapshot.statistics.filter { stat in
                (table == nil || stat.table == table) && (column == nil || stat.column == column)
            }
        }
    }

    public func configurations(scope: String? = nil, key: String? = nil) -> [ConfigurationEntry] {
        queue.sync {
            snapshot.configurations.filter { entry in
                (scope == nil || entry.scope == scope) && (key == nil || entry.key == key)
            }
        }
    }

    public func structurePreferences(table: String? = nil) -> [StructurePreference] {
        queue.sync {
            guard let table = table else { return snapshot.structures }
            return snapshot.structures.filter { $0.table == table }
        }
    }

    // MARK: - Helpers
    private func upsertPhysicalLocked(logicalId: UUID?, kind: PhysicalKind, path: String?, pageSize: Int?, sizeBytes: UInt64?) {
        let now = Date()
        if let path = path, let idx = snapshot.physical.firstIndex(where: { $0.path == path }) {
            snapshot.physical[idx].logicalId = logicalId
            snapshot.physical[idx].kind = kind
            snapshot.physical[idx].metadata = mergedMetadata(snapshot.physical[idx].metadata, ["pageSize": stringOpt(pageSize), "sizeBytes": stringOpt(sizeBytes)])
            snapshot.physical[idx].updatedAt = now
            return
        }
        var metadata: [String: String] = [:]
        if let pageSize = pageSize { metadata["pageSize"] = String(pageSize) }
        if let sizeBytes = sizeBytes { metadata["sizeBytes"] = String(sizeBytes) }
        let physical = PhysicalObject(id: UUID(), logicalId: logicalId, kind: kind, path: path, metadata: metadata, createdAt: now, updatedAt: now)
        snapshot.physical.append(physical)
    }

    private func fileSize(path: String) -> UInt64? {
        let attrs = try? FileManager.default.attributesOfItem(atPath: path)
        return (attrs?[.size] as? NSNumber)?.uint64Value
    }

    private func mergedMetadata(_ lhs: [String: String], _ rhs: [String: String]) -> [String: String] {
        var result = lhs
        for (k, v) in rhs where v != "nil" {
            result[k] = v
        }
        return result
    }

    private func persistLocked() throws {
        let data = try encoder.encode(snapshot)
        try data.write(to: fileURL, options: .atomic)
    }

    private func stringOpt<T>(_ value: T?) -> String {
        if let v = value {
            return String(describing: v)
        }
        return "nil"
    }
}

