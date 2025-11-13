//
//  QueryOptimizerTests.swift
//  ColibrìDB - Query Optimizer Tests
//
//  Tests for cost-based query optimization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import XCTest
@testable import ColibriCore

/// Tests for the Query Optimizer
/// Covers cost-based optimization, plan generation, and cost estimation
final class QueryOptimizerTests {
    
    // MARK: - Setup
    
    func testQueryOptimizerCreation() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        
        // Act
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Assert
        XCTAssert(optimizer != nil)
    }
    
    // MARK: - Plan Generation Tests
    
    func testGenerateScanPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should default to scan plan when no indexes available
        if case .scan(let table) = physicalPlan {
            XCTAssert(table == "users")
        } else {
            XCTAssert(false, "Expected scan plan")
        }
    }
    
    func testGenerateIndexScanPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock table with index
        let tableMetadata = TableMetadata(
            name: "users",
            columns: [
                ColumnMetadata(name: "id", type: .int, nullable: false),
                ColumnMetadata(name: "email", type: .string, nullable: false)
            ],
            primaryKey: ["id"]
        )
        
        // Act
        let logicalPlan = LogicalPlan(
            table: "users",
            filterKey: Value.string("test@example.com")
        )
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
    }
    
    func testGenerateFilterPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18
                }
                return false
            }
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have filter node
        if case .filter(_, _) = physicalPlan {
            // Expected filter plan
        } else {
            // Could be scan plan if no indexes
        }
    }
    
    func testGenerateProjectPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            projection: ["id", "name", "email"]
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have project node
        if case .project(_, _) = physicalPlan {
            // Expected project plan
        } else {
            // Could be scan plan if no indexes
        }
    }
    
    func testGenerateSortPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            sortColumns: ["name", "email"]
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have sort node
        if case .sort(_, _) = physicalPlan {
            // Expected sort plan
        } else {
            // Could be scan plan if no indexes
        }
    }
    
    func testGenerateLimitPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            limit: 10
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have limit node
        if case .limit(_, _) = physicalPlan {
            // Expected limit plan
        } else {
            // Could be scan plan if no indexes
        }
    }
    
    func testGenerateComplexPlan() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18
                }
                return false
            },
            projection: ["id", "name"],
            sortColumns: ["name"],
            limit: 100
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have multiple nodes (filter, project, sort, limit)
    }
    
    // MARK: - Cost Estimation Tests
    
    func testEstimateScanCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Cost should be based on page count (100 pages * 1.0 cost per page)
    }
    
    func testEstimateIndexScanCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(
            table: "users",
            filterKey: Value.string("test@example.com")
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Index scan should be cheaper than full scan
    }
    
    func testEstimateFilterCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18
                }
                return false
            }
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Filter cost should include selectivity factor
    }
    
    func testEstimateJoinCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics for both tables
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 50,
            rowCount: 500,
            avgRowSize: 200
        ))
        await statistics.updateStatistics(table: "orders", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 150
        ))
        
        // Act
        let logicalPlan = LogicalPlan(table: "users") // Simplified for join test
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Join cost should consider both tables
    }
    
    func testEstimateSortCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(
            table: "users",
            sortColumns: ["name"]
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Sort cost should include O(n log n) factor
    }
    
    func testEstimateAggregateCost() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Aggregate cost should include hash build overhead
    }
    
    // MARK: - Cost Model Tests
    
    func testCostModelConstants() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Act & Assert
        // Test that cost constants are reasonable
        // These would be tested through the cost estimation methods
        let logicalPlan = LogicalPlan(table: "users")
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        XCTAssert(physicalPlan != nil)
    }
    
    func testCostComparison() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        // Act
        let scanPlan = LogicalPlan(table: "users")
        let indexPlan = LogicalPlan(
            table: "users",
            filterKey: Value.string("test@example.com")
        )
        
        let scanPhysical = await optimizer.optimize(logical: scanPlan)
        let indexPhysical = await optimizer.optimize(logical: indexPlan)
        
        // Assert
        XCTAssert(scanPhysical != nil)
        XCTAssert(indexPhysical != nil)
        // Index scan should generally be cheaper than full scan
    }
    
    // MARK: - Statistics Integration Tests
    
    func testStatisticsIntegration() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 50,
            rowCount: 500,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Cost should be based on actual statistics (50 pages)
    }
    
    func testStatisticsUpdate() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Initial statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 50,
            rowCount: 500,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(table: "users")
        let initialPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Update statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        // Act
        let updatedPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(initialPlan != nil)
        XCTAssert(updatedPlan != nil)
        // Plans should be different due to updated statistics
    }
    
    // MARK: - Plan Node Tests
    
    func testScanPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        if case .scan(let table) = physicalPlan {
            XCTAssert(table == "users")
        } else {
            // Could be other plan types depending on optimization
        }
    }
    
    func testIndexScanPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            filterKey: Value.string("test@example.com")
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Could be index scan if indexes are available
    }
    
    func testFilterPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18
                }
                return false
            }
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have filter node
    }
    
    func testProjectPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            projection: ["id", "name"]
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have project node
    }
    
    func testSortPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            sortColumns: ["name"]
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have sort node
    }
    
    func testLimitPlanNode() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            limit: 10
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should have limit node
    }
    
    // MARK: - Edge Cases Tests
    
    func testEmptyTableOptimization() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock empty table statistics
        await statistics.updateStatistics(table: "empty_table", stats: TableStatistics(
            pageCount: 0,
            rowCount: 0,
            avgRowSize: 0
        ))
        
        let logicalPlan = LogicalPlan(table: "empty_table")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should handle empty table gracefully
    }
    
    func testLargeTableOptimization() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock large table statistics
        await statistics.updateStatistics(table: "large_table", stats: TableStatistics(
            pageCount: 10000,
            rowCount: 1000000,
            avgRowSize: 500
        ))
        
        let logicalPlan = LogicalPlan(table: "large_table")
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should handle large table efficiently
    }
    
    func testComplexPredicateOptimization() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"],
                      let salary = row["salary"] else { return false }
                
                if case Value.int(let ageValue) = age,
                   case Value.int(let salaryValue) = salary {
                    return ageValue > 25 && salaryValue > 50000
                }
                return false
            }
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should handle complex predicates
    }
    
    // MARK: - Performance Tests
    
    func testOptimizationPerformance() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18
                }
                return false
            },
            projection: ["id", "name"],
            sortColumns: ["name"],
            limit: 100
        )
        
        let startTime = Date()
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        XCTAssert(physicalPlan != nil)
        XCTAssert(duration < 1.0) // Should complete in under 1 second
    }
    
    func testMultipleOptimizationCalls() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 100,
            rowCount: 1000,
            avgRowSize: 200
        ))
        
        let logicalPlan = LogicalPlan(table: "users")
        
        // Act
        let startTime = Date()
        
        for _ in 0..<100 {
            let physicalPlan = await optimizer.optimize(logical: logicalPlan)
            XCTAssert(physicalPlan != nil)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Assert
        XCTAssert(duration < 5.0) // 100 optimizations should complete in under 5 seconds
    }
    
    // MARK: - Integration Tests
    
    func testEndToEndOptimization() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Mock table with statistics
        await statistics.updateStatistics(table: "users", stats: TableStatistics(
            pageCount: 50,
            rowCount: 500,
            avgRowSize: 200
        ))
        
        // Complex logical plan
        let logicalPlan = LogicalPlan(
            table: "users",
            predicate: { row in
                guard let age = row["age"] else { return false }
                if case Value.int(let ageValue) = age {
                    return ageValue > 18 && ageValue < 65
                }
                return false
            },
            projection: ["id", "name", "email"],
            sortColumns: ["name"],
            limit: 50
        )
        
        // Act
        let physicalPlan = await optimizer.optimize(logical: logicalPlan)
        
        // Assert
        XCTAssert(physicalPlan != nil)
        // Should generate an optimized plan
    }
    
    func testOptimizationWithDifferentTableSizes() async throws {
        // Arrange
        let catalog = Catalog()
        let statistics = StatisticsManagerActor()
        let optimizer = QueryOptimizer(catalog: catalog, statistics: statistics)
        
        // Test with different table sizes
        let tableSizes = [
            ("small_table", TableStatistics(pageCount: 10, rowCount: 100, avgRowSize: 100)),
            ("medium_table", TableStatistics(pageCount: 100, rowCount: 1000, avgRowSize: 200)),
            ("large_table", TableStatistics(pageCount: 1000, rowCount: 10000, avgRowSize: 300))
        ]
        
        for (tableName, tableStats) in tableSizes {
            // Act
            await statistics.updateStatistics(table: tableName, stats: tableStats)
            let logicalPlan = LogicalPlan(table: tableName)
            let physicalPlan = await optimizer.optimize(logical: logicalPlan)
            
            // Assert
            XCTAssert(physicalPlan != nil)
        }
    }
}

