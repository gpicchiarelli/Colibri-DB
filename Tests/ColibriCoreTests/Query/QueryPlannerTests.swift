//
//  QueryPlannerTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Query Planner Tests", .serialized)
struct QueryPlannerTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        
        // Setup test data
        try db.createTable("users")
        let tid = try db.begin()
        for i in 1...10 {
            let row: Row = [
                "id": .int(Int64(i)),
                "name": .string("User\(i)"),
                "age": .int(Int64(20 + i))
            ]
            _ = try db.insert(table: "users", row: row, tid: tid)
        }
        try db.commit(tid)
        
        return db
    }
    
    @Test("Create query planner")
    func testCreatePlanner() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        
        #expect(planner != nil)
    }
    
    @Test("Plan simple table scan")
    func testPlanTableScan() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        let request = QueryRequest(root: QueryTableRef(name: "users"))
        let context = ExecutionContext(tid: nil, database: db)
        
        let plan = try planner.plan(request: request, context: context)
        
        #expect(plan != nil)
    }
    
    @Test("Plan query with filter")
    func testPlanWithFilter() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        
        let predicate = QueryPredicate(
            column: "age",
            op: .greaterOrEqual,
            value: .int(25)
        )
        
        let request = QueryRequest(
            root: QueryTableRef(name: "users", predicates: [predicate])
        )
        
        let context = ExecutionContext(tid: nil, database: db)
        let plan = try planner.plan(request: request, context: context)
        
        #expect(plan != nil)
    }
    
    @Test("Plan query with projection")
    func testPlanWithProjection() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        
        let request = QueryRequest(
            root: QueryTableRef(
                name: "users",
                projection: ["id", "name"]
            )
        )
        
        let context = ExecutionContext(tid: nil, database: db)
        let plan = try planner.plan(request: request, context: context)
        
        #expect(plan != nil)
    }
    
    @Test("Plan query with limit")
    func testPlanWithLimit() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        
        let request = QueryRequest(
            root: QueryTableRef(name: "users"),
            limit: 5
        )
        
        let context = ExecutionContext(tid: nil, database: db)
        let plan = try planner.plan(request: request, context: context)
        
        #expect(plan != nil)
    }
    
    @Test("Execute simple scan plan")
    func testExecuteScan() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        let request = QueryRequest(root: QueryTableRef(name: "users"))
        let context = ExecutionContext(tid: nil, database: db)
        
        let plan = try planner.plan(request: request, context: context)
        let results = try QueryExecutor.execute(plan: plan, context: context)
        
        #expect(results.count == 10)
    }
    
    @Test("Execute filtered query")
    func testExecuteFiltered() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        
        let predicate = QueryPredicate(
            column: "age",
            op: .greaterOrEqual,
            value: .int(25)
        )
        
        let request = QueryRequest(
            root: QueryTableRef(name: "users", predicates: [predicate])
        )
        
        let context = ExecutionContext(tid: nil, database: db)
        let plan = try planner.plan(request: request, context: context)
        let results = try QueryExecutor.execute(plan: plan, context: context)
        
        // Should have filtered results
        #expect(results.count < 10)
        
        // All results should match predicate
        for row in results {
            if case .int(let age) = row["users.age"] ?? .null {
                #expect(age >= 25)
            }
        }
    }
    
    @Test("Execute query with limit")
    func testExecuteLimit() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let planner = QueryPlanner(database: db)
        let request = QueryRequest(
            root: QueryTableRef(name: "users"),
            limit: 3
        )
        
        let context = ExecutionContext(tid: nil, database: db)
        let plan = try planner.plan(request: request, context: context)
        let results = try QueryExecutor.execute(plan: plan, context: context)
        
        #expect(results.count == 3)
    }
}

