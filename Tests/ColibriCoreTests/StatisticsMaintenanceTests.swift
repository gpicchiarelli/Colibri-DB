//
//  StatisticsMaintenanceTests.swift
//  ColibrìDB - Statistics Maintenance Tests
//
//  Tests for query optimizer statistics collection and maintenance
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import XCTest
@testable import ColibriCore

/// Tests for the Statistics Maintenance system
/// Covers table statistics, column statistics, histograms, and auto-analyze
final class StatisticsMaintenanceTests {
    
    // MARK: - Setup
    
    func testStatisticsManagerCreation() async throws {
        // Arrange & Act
        let statsManager = StatisticsMaintenanceManager()
        
        // Assert
        XCTAssertNotNil(statsManager)
    }
    
    // MARK: - Table Statistics Tests
    
    func testTableStatisticsCreation() async throws {
        // Arrange
        let stats = TableStatisticsMaintenance(pageCount: 100, rowCount: 1000, avgRowSize: 200)
        
        // Assert
        XCTAssert(stats.pageCount == 100)
        XCTAssert(stats.rowCount == 1000)
        XCTAssert(stats.avgRowSize == 200)
        XCTAssert(stats.deadTuples == 0)
        XCTAssert(stats.modifications == 0)
    }
    
    func testTableStatisticsDefaultValues() async throws {
        // Arrange
        let stats = TableStatisticsMaintenance()
        
        // Assert
        XCTAssert(stats.pageCount == 0)
        XCTAssert(stats.rowCount == 0)
        XCTAssert(stats.avgRowSize == 0)
        XCTAssert(stats.deadTuples == 0)
        XCTAssert(stats.modifications == 0)
    }
    
    func testTableStatisticsAliases() async throws {
        // Arrange
        let stats = TableStatisticsMaintenance(pageCount: 50, rowCount: 500, avgRowSize: 150)
        
        // Assert
        XCTAssert(stats.avgRowSize == 150)
    }
    
    // MARK: - Column Statistics Tests
    
    func testColumnStatisticsCreation() async throws {
        // Arrange
        let colStats = ColumnStatistics(
            columnName: "age",
            distinctCount: 100,
            nullCount: 10,
            minValue: "18",
            maxValue: "65",
            avgSize: 4
        )
        
        // Assert
        XCTAssert(colStats.columnName == "age")
        XCTAssert(colStats.distinctValues == 100)
        XCTAssert(colStats.nullFraction == 10)
        XCTAssert(colStats.minValue == "18")
        XCTAssert(colStats.maxValue == "65")
        XCTAssert(colStats.avgWidth == 4)
    }
    
    func testColumnStatisticsDefaultValues() async throws {
        // Arrange
        let colStats = ColumnStatistics(columnName: "test_column")
        
        // Assert
        XCTAssert(colStats.columnName == "test_column")
        XCTAssert(colStats.distinctValues == 0)
        XCTAssert(colStats.nullFraction == 0)
        XCTAssert(colStats.minValue == nil)
        XCTAssert(colStats.maxValue == nil)
        XCTAssert(colStats.avgWidth == 0)
        XCTAssert(colStats.mostCommonValues.isEmpty)
        XCTAssert(colStats.mostCommonFreqs.isEmpty)
        XCTAssert(colStats.histogram == nil)
        XCTAssert(colStats.correlation == 0)
    }
    
    func testColumnStatisticsAliases() async throws {
        // Arrange
        let colStats = ColumnStatistics(
            columnName: "test",
            distinctCount: 50,
            nullCount: 5,
            minValue: "1",
            maxValue: "100",
            avgSize: 8
        )
        
        // Assert
        XCTAssert(colStats.distinctCount == colStats.distinctValues)
        XCTAssert(colStats.nullCount == colStats.nullFraction)
        XCTAssert(colStats.avgSize == colStats.avgWidth)
    }
    
    func testColumnStatisticsSelectivity() async throws {
        // Arrange
        let colStats = ColumnStatistics(
            columnName: "status",
            distinctCount: 10,
            nullCount: 0,
            minValue: "active",
            maxValue: "inactive",
            avgSize: 10
        )
        
        // Act
        let selectivity1 = colStats.selectivity(totalRows: 100)
        let selectivity2 = colStats.selectivity(totalRows: 1000)
        let selectivity3 = colStats.selectivity(totalRows: 0)
        
        // Assert
        XCTAssert(selectivity1 == 0.1) // 10/100
        XCTAssert(selectivity2 == 0.01) // 10/1000
        XCTAssert(selectivity3 == 1.0) // Default for zero rows
    }
    
    // MARK: - Index Statistics Tests
    
    func testIndexStatisticsCreation() async throws {
        // Arrange
        let indexStats = IndexStatistics(indexName: "test_index")
        
        // Assert
        XCTAssert(indexStats.size == 0)
        XCTAssert(indexStats.height == 0)
        XCTAssert(indexStats.selectivity == 100.0)
    }
    
    func testIndexStatisticsAliases() async throws {
        // Arrange
        var indexStats = IndexStatistics(indexName: "test_index")
        indexStats.size = 100
        
        // Assert
        XCTAssert(indexStats.size == 100)
    }
    
    // MARK: - Histogram Tests
    
    func testHistogramCreation() async throws {
        // Arrange
        let buckets = [
            HistogramBucket(lowerBound: "1", upperBound: "10", rowCount: 100, distinctCount: 10),
            HistogramBucket(lowerBound: "11", upperBound: "20", rowCount: 150, distinctCount: 15)
        ]
        let histogram = Histogram(type: .equiDepth, buckets: buckets)
        
        // Assert
        XCTAssert(histogram.type == .equiDepth)
        XCTAssert(histogram.buckets.count == 2)
        XCTAssert(histogram.bucketCount == 2)
    }
    
    func testHistogramTypes() async throws {
        // Arrange
        let buckets = [HistogramBucket(lowerBound: "1", upperBound: "10", rowCount: 100, distinctCount: 10)]
        
        // Act & Assert
        let equiDepth = Histogram(type: .equiDepth, buckets: buckets)
        let equiWidth = Histogram(type: .equiWidth, buckets: buckets)
        let maxDiff = Histogram(type: .maxDiff, buckets: buckets)
        let vOptimal = Histogram(type: .vOptimal, buckets: buckets)
        
        XCTAssert(equiDepth.type == .equiDepth)
        XCTAssert(equiWidth.type == .equiWidth)
        XCTAssert(maxDiff.type == .maxDiff)
        XCTAssert(vOptimal.type == .vOptimal)
    }
    
    func testHistogramBucket() async throws {
        // Arrange
        let bucket = HistogramBucket(
            lowerBound: "1",
            upperBound: "10",
            rowCount: 100,
            distinctCount: 10
        )
        
        // Assert
        XCTAssert(bucket.minValue == "1")
        XCTAssert(bucket.maxValue == "10")
        XCTAssert(bucket.frequency == 100)
        XCTAssert(bucket.distinctValues == 10)
    }
    
    // MARK: - HyperLogLog Tests
    
    func testHyperLogLogCreation() async throws {
        // Arrange
        let hll = HyperLogLogSketch(precision: 12)
        
        // Assert
        XCTAssert(hll.precision == 12)
        XCTAssert(hll.registers.count == 4096) // 2^12
        XCTAssert(hll.estimatedCardinality == 0)
    }
    
    func testHyperLogLogDefaultPrecision() async throws {
        // Arrange
        let hll = HyperLogLogSketch()
        
        // Assert
        XCTAssert(hll.precision == 12)
        XCTAssert(hll.registers.count == 4096)
    }
    
    func testHyperLogLogAddValue() async throws {
        // Arrange
        var hll = HyperLogLogSketch(precision: 8)
        
        // Act
        hll.add(value: "test1")
        hll.add(value: "test2")
        hll.add(value: "test1") // Duplicate
        
        // Assert
        XCTAssert(hll.estimatedCardinality >= 0)
        XCTAssert(hll.estimatedCardinality <= 3)
    }
    
    func testHyperLogLogEstimate() async throws {
        // Arrange
        var hll = HyperLogLogSketch(precision: 8)
        
        // Act
        for i in 0..<100 {
            hll.add(value: "value_\(i)")
        }
        
        let estimate = hll.estimate()
        
        // Assert
        XCTAssert(estimate >= 0)
        XCTAssert(estimate <= 100)
    }
    
    // MARK: - ANALYZE Operations Tests
    
    func testStartAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await statsManager.startAnalyze(table: "test_table")
        
        // Assert
        // Should complete without error
    }
    
    func testAnalyzeTable() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 100)
    }
    
    func testAnalyzeEmptyTable() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows: [Row] = []
        
        // Act
        await statsManager.analyze(table: "empty_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("empty_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 0)
    }
    
    func testAnalyzeTableWithColumns() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 50)
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 50)
        
        // Check column statistics
        let colStats = await statsManager.getColumnStatistics("test_table", column: "id")
        XCTAssert(colStats != nil)
    }
    
    // MARK: - Incremental Updates Tests
    
    func testRecordModification() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.recordModification(table: "test_table")
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        XCTAssert(tableStats?.modifications == 1)
    }
    
    func testUpdateRowCount() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.updateRowCount(table: "test_table", delta: 50)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        XCTAssert(tableStats?.rowCount == 150)
    }
    
    func testUpdateRowCountNegative() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.updateRowCount(table: "test_table", delta: -30)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        XCTAssert(tableStats?.rowCount == 70)
    }
    
    // MARK: - Auto-Analyze Tests
    
    func testShouldAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let shouldAnalyze = await statsManager.shouldAnalyze("test_table")
        
        // Assert
        XCTAssert(shouldAnalyze == true) // Should be true for new table
    }
    
    func testShouldAnalyzeAfterAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let shouldAnalyze = await statsManager.shouldAnalyze("test_table")
        
        // Assert
        XCTAssert(shouldAnalyze == false) // Should be false after recent analyze
    }
    
    func testSetAutoAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await statsManager.setAutoAnalyze(enabled: false)
        
        // Assert
        // Should complete without error
    }
    
    // MARK: - Cardinality Estimation Tests
    
    func testEstimateCardinality() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let cardinality = await statsManager.estimateCardinality(table: "test_table", predicate: "age > 18")
        
        // Assert
        XCTAssert(cardinality >= 0)
        XCTAssert(cardinality <= 1000)
    }
    
    func testEstimateCardinalityDefault() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let cardinality = await statsManager.estimateCardinality(table: "non_existent", predicate: "age > 18")
        
        // Assert
        XCTAssert(cardinality == 1000) // Default estimate
    }
    
    func testEstimateSelectivity() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let selectivity = await statsManager.estimateSelectivity(table: "test_table", column: "id", predicate: "id = 1")
        
        // Assert
        XCTAssert(selectivity >= 0.0)
        XCTAssert(selectivity <= 1.0)
    }
    
    func testEstimateSelectivityDefault() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let selectivity = await statsManager.estimateSelectivity(table: "non_existent", column: "id", predicate: "id = 1")
        
        // Assert
        XCTAssert(selectivity == 0.1) // Default 10%
    }
    
    // MARK: - Query Methods Tests
    
    func testGetTableStatistics() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let tableStats = await statsManager.getTableStatistics("test_table")
        
        // Assert
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 100)
    }
    
    func testGetTableStatisticsNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let tableStats = await statsManager.getTableStatistics("non_existent")
        
        // Assert
        XCTAssert(tableStats == nil)
    }
    
    func testGetColumnStatistics() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let colStats = await statsManager.getColumnStatistics("test_table", column: "id")
        
        // Assert
        XCTAssert(colStats != nil)
        XCTAssert(colStats?.columnName == "id")
    }
    
    func testGetColumnStatisticsNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let colStats = await statsManager.getColumnStatistics("non_existent", column: "id")
        
        // Assert
        XCTAssert(colStats == nil)
    }
    
    func testGetIndexStats() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let indexStats = await statsManager.getIndexStats(indexName: "test_index")
        
        // Assert
        XCTAssert(indexStats == nil) // No index stats by default
    }
    
    func testGetFreshnessScore() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let freshness = await statsManager.getFreshnessScore(table: "test_table")
        
        // Assert
        XCTAssert(freshness >= 0.0)
        XCTAssert(freshness <= 1.0)
    }
    
    func testGetFreshnessScoreNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let freshness = await statsManager.getFreshnessScore(table: "non_existent")
        
        // Assert
        XCTAssert(freshness == 0.0)
    }
    
    // MARK: - Performance Tests
    
    func testAnalyzePerformance() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        
        let startTime = Date()
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        XCTAssert(duration < 5.0) // Should complete in reasonable time
    }
    
    func testBulkAnalyzeOperations() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let tableCount = 10
        let rowsPerTable = 100
        
        let startTime = Date()
        
        // Act
        for i in 0..<tableCount {
            let rows = createTestRows(count: rowsPerTable)
            await statsManager.analyze(table: "table_\(i)", rows: rows)
        }
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        XCTAssert(duration < 10.0) // Should complete in reasonable time
    }
    
    func testConcurrentAnalyzeOperations() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<5 {
                group.addTask { @Sendable in
                    let rows = TestDataGenerator.generateTestRows(count: 100)
                    await statsManager.analyze(table: "concurrent_table_\(i)", rows: rows)
                }
            }
        }
        
        // Assert
        // Should complete without errors
    }
    
    // MARK: - Edge Cases Tests
    
    func testAnalyzeWithEmptyRows() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows: [Row] = []
        
        // Act
        await statsManager.analyze(table: "empty_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("empty_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 0)
    }
    
    func testAnalyzeWithSingleRow() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1)
        
        // Act
        await statsManager.analyze(table: "single_row_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("single_row_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 1)
    }
    
    func testAnalyzeWithLargeDataset() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 10000)
        
        // Act
        await statsManager.analyze(table: "large_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("large_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 10000)
    }
    
    func testAnalyzeWithNullValues() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRowsWithNulls(count: 100)
        
        // Act
        await statsManager.analyze(table: "nulls_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("nulls_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 100)
    }
    
    // MARK: - Integration Tests
    
    func testCompleteStatisticsWorkflow() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        
        // Act & Assert - Analyze
        await statsManager.analyze(table: "workflow_table", rows: rows)
        let tableStats = await statsManager.getTableStatistics("workflow_table")
        XCTAssert(tableStats?.rowCount == 1000)
        
        // Act & Assert - Record modifications
        await statsManager.recordModification(table: "workflow_table")
        let modifiedStats = await statsManager.getTableStatistics("workflow_table")
        XCTAssert(modifiedStats?.modifications == 1)
        
        // Act & Assert - Update row count
        await statsManager.updateRowCount(table: "workflow_table", delta: 100)
        let updatedStats = await statsManager.getTableStatistics("workflow_table")
        XCTAssert(updatedStats?.rowCount == 1100)
        
        // Act & Assert - Estimate cardinality
        let cardinality = await statsManager.estimateCardinality(table: "workflow_table", predicate: "id > 500")
        XCTAssert(cardinality >= 0)
        
        // Act & Assert - Estimate selectivity
        let selectivity = await statsManager.estimateSelectivity(table: "workflow_table", column: "id", predicate: "id = 1")
        XCTAssert(selectivity >= 0.0)
        XCTAssert(selectivity <= 1.0)
    }
    
    func testStatisticsConsistency() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        
        // Act
        await statsManager.analyze(table: "consistency_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("consistency_table")
        XCTAssert(tableStats != nil)
        XCTAssert(tableStats?.rowCount == 100)
        XCTAssert((tableStats?.pageCount ?? 0) > 0)
        XCTAssert((tableStats?.avgRowSize ?? 0) > 0)
    }
    
    // MARK: - Helper Methods
    
    private func createTestRows(count: Int) -> [Row] {
        var rows: [Row] = []
        for i in 0..<count {
            let row: Row = [
                "id": Value.int(Int64(i)),
                "name": Value.string("user_\(i)"),
                "age": Value.int(Int64(18 + (i % 50))),
                "email": Value.string("user\(i)@example.com")
            ]
            rows.append(row)
        }
        return rows
    }
    
    private func createTestRowsWithNulls(count: Int) -> [Row] {
        var rows: [Row] = []
        for i in 0..<count {
            let row: Row = [
                "id": Value.int(Int64(i)),
                "name": i % 2 == 0 ? Value.string("user_\(i)") : .null,
                "age": i % 3 == 0 ? .null : Value.int(Int64(18 + (i % 50))),
                "email": Value.string("user\(i)@example.com")
            ]
            rows.append(row)
        }
        return rows
    }
}

