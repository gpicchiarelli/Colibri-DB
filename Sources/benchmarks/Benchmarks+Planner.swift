import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Planner base
    static func runPlannerJoin(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }

        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        config.walEnabled = false
        config.dataDir = tempDir.path
        let db = Database(config: config)
        try db.createTable("users")
        try db.createTable("orders")
        for u in 0..<iterations {
            _ = try db.insert(into: "users", row: ["id": .int(Int64(u)), "region": .string(u % 2 == 0 ? "EU" : "US")])
            _ = try db.insert(into: "orders", row: ["id": .int(Int64(u)), "user_id": .int(Int64(u)), "total": .double(Double.random(in: 1..<100))])
        }
        try db.createIndex(name: "idx_orders_user", on: "orders", columns: ["user_id"], using: "BTree")
        try db.rebuildIndexBulk(table: "orders", index: "idx_orders_user")

        let predicate = QueryPredicate(column: "region", op: .equals, value: .string("EU"), selectivityHint: 0.5)
        let users = QueryTableRef(name: "users", predicates: [predicate], projection: ["id", "region"])
        let orders = QueryTableRef(name: "orders", alias: "o", projection: ["id", "user_id", "total"], indexHint: "idx_orders_user")
        let join = QueryJoinSpec(table: orders, leftColumns: ["users.id"], rightColumns: ["o.user_id"])
        let request = QueryRequest(root: users, joins: [join], orderBy: [SortKey(column: "o.total", ascending: false)], parallelism: 2)

        let clock = ContinuousClock(); let start = clock.now
        let rows = try db.executeQuery(request)
        precondition(!rows.isEmpty)
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.plannerJoin.rawValue, iterations: rows.count, elapsed: elapsed)
    }

    // MARK: - Planner estesi
    static func runPlannerIndexScan(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("users")
        for i in 0..<iterations { _ = try db.insert(into: "users", row: ["id": .int(Int64(i)), "name": .string("u\(i)")]) }
        try db.createIndex(name: "idx_users_id", on: "users", columns: ["id"], using: "BTree")
        try db.rebuildIndexBulk(table: "users", index: "idx_users_id")
        let pred = QueryPredicate(column: "id", op: .equals, value: .int(Int64(iterations / 2)))
        let users = QueryTableRef(name: "users", predicates: [pred], projection: ["id", "name"], indexHint: "idx_users_id")
        let req = QueryRequest(root: users, joins: [], limit: nil, parallelism: 1)
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            let qn = min(1_000, max(1, iterations))
            var lat: [Double] = []; lat.reserveCapacity(qn)
            var rowsFetched = 0
            for _ in 0..<qn {
                let t0 = clock.now
                let out = try db.executeQuery(req)
                let t1 = clock.now
                rowsFetched &+= out.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(rowsFetched > 0)
            return BenchmarkResult(name: Scenario.plannerIndexScan.rawValue, iterations: qn, elapsed: elapsed, latenciesMs: lat, metadata: ["rows_fetched":"\(rowsFetched)"])
        } else {
            let out = try db.executeQuery(req)
            let elapsed = clock.now - start
            precondition(!out.isEmpty)
            return BenchmarkResult(name: Scenario.plannerIndexScan.rawValue, iterations: out.count, elapsed: elapsed)
        }
    }

    static func runPlannerSortLimit(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("orders")
        for i in 0..<iterations { _ = try db.insert(into: "orders", row: ["id": .int(Int64(i)), "total": .double(Double.random(in: 1..<1000))]) }
        let orders = QueryTableRef(name: "orders", projection: ["id", "total"])
        let req = QueryRequest(root: orders,
                               joins: [],
                               orderBy: [SortKey(column: "orders.total", ascending: false)],
                               limit: max(1, iterations / 10),
                               parallelism: 2)
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            let qn = min(1_000, max(1, iterations / 10))
            var lat: [Double] = []; lat.reserveCapacity(qn)
            var total = 0
            for _ in 0..<qn {
                let t0 = clock.now
                let out = try db.executeQuery(req)
                let t1 = clock.now
                total &+= out.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(total > 0)
            return BenchmarkResult(name: Scenario.plannerSortLimit.rawValue, iterations: qn, elapsed: elapsed, latenciesMs: lat, metadata: ["rows_total":"\(total)"])
        } else {
            let out = try db.executeQuery(req)
            let elapsed = clock.now - start
            precondition(!out.isEmpty)
            return BenchmarkResult(name: Scenario.plannerSortLimit.rawValue, iterations: out.count, elapsed: elapsed)
        }
    }
}


