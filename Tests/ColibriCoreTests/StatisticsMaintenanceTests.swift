//
//  StatisticsMaintenanceTests.swift
//  ColibrìDB - Statistics Maintenance Tests
//
//  Tests for query optimizer statistics collection and maintenance
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Testing
@testable import ColibriCore

/// Tests for the Statistics Maintenance system
/// Covers table statistics, column statistics, histograms, and auto-analyze
struct StatisticsMaintenanceTests {
    
    // MARK: - Setup
    
    @Test func testStatisticsManagerCreation() async throws {
        // Arrange & Act
        let statsManager = StatisticsMaintenanceManager()
        
        // Assert
        #expect(statsManager != nil)
    }
    
    // MARK: - Table Statistics Tests
    
    @Test func testTableStatisticsCreation() async throws {
        // Arrange
        let stats = TableStatistics(pageCount: 100, rowCount: 1000, avgRowSize: 200)
        
        // Assert
        #expect(stats.pageCount == 100)
        #expect(stats.rowCount == 1000)
        #expect(stats.avgRowSize == 200)
        #expect(stats.deadTuples == 0)
        #expect(stats.modifications == 0)
    }
    
    @Test func testTableStatisticsDefaultValues() async throws {
        // Arrange
        let stats = TableStatistics()
        
        // Assert
        #expect(stats.pageCount == 0)
        #expect(stats.rowCount == 0)
        #expect(stats.avgRowSize == 0)
        #expect(stats.deadTuples == 0)
        #expect(stats.modifications == 0)
    }
    
    @Test func testTableStatisticsAliases() async throws {
        // Arrange
        let stats = TableStatistics(pageCount: 50, rowCount: 500, avgRowSize: 150)
        
        // Assert
        #expect(stats.avgRowSize == stats.tupleSize)
    }
    
    // MARK: - Column Statistics Tests
    
    @Test func testColumnStatisticsCreation() async throws {
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
        #expect(colStats.columnName == "age")
        #expect(colStats.distinctValues == 100)
        #expect(colStats.nullFraction == 10)
        #expect(colStats.minValue == "18")
        #expect(colStats.maxValue == "65")
        #expect(colStats.avgWidth == 4)
    }
    
    @Test func testColumnStatisticsDefaultValues() async throws {
        // Arrange
        let colStats = ColumnStatistics(columnName: "test_column")
        
        // Assert
        #expect(colStats.columnName == "test_column")
        #expect(colStats.distinctValues == 0)
        #expect(colStats.nullFraction == 0)
        #expect(colStats.minValue == nil)
        #expect(colStats.maxValue == nil)
        #expect(colStats.avgWidth == 0)
        #expect(colStats.mostCommonValues.isEmpty)
        #expect(colStats.mostCommonFreqs.isEmpty)
        #expect(colStats.histogram == nil)
        #expect(colStats.correlation == 0)
    }
    
    @Test func testColumnStatisticsAliases() async throws {
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
        #expect(colStats.distinctCount == colStats.distinctValues)
        #expect(colStats.nullCount == colStats.nullFraction)
        #expect(colStats.avgSize == colStats.avgWidth)
    }
    
    @Test func testColumnStatisticsSelectivity() async throws {
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
        #expect(selectivity1 == 0.1) // 10/100
        #expect(selectivity2 == 0.01) // 10/1000
        #expect(selectivity3 == 1.0) // Default for zero rows
    }
    
    // MARK: - Index Statistics Tests
    
    @Test func testIndexStatisticsCreation() async throws {
        // Arrange
        let indexStats = IndexStatistics()
        
        // Assert
        #expect(indexStats.distinctKeys == 0)
        #expect(indexStats.height == 0)
        #expect(indexStats.pages == 0)
        #expect(indexStats.leafPages == indexStats.pages)
        #expect(indexStats.avgFillFactor == 0.0)
        #expect(indexStats.indexSize == 0)
    }
    
    @Test func testIndexStatisticsAliases() async throws {
        // Arrange
        var indexStats = IndexStatistics()
        indexStats.pages = 100
        
        // Assert
        #expect(indexStats.leafPages == 100)
    }
    
    // MARK: - Histogram Tests
    
    @Test func testHistogramCreation() async throws {
        // Arrange
        let buckets = [
            HistogramBucket(lowerBound: "1", upperBound: "10", rowCount: 100, distinctCount: 10),
            HistogramBucket(lowerBound: "11", upperBound: "20", rowCount: 150, distinctCount: 15)
        ]
        let histogram = Histogram(type: .equiDepth, buckets: buckets)
        
        // Assert
        #expect(histogram.type == .equiDepth)
        #expect(histogram.buckets.count == 2)
        #expect(histogram.bucketCount == 2)
    }
    
    @Test func testHistogramTypes() async throws {
        // Arrange
        let buckets = [HistogramBucket(lowerBound: "1", upperBound: "10", rowCount: 100, distinctCount: 10)]
        
        // Act & Assert
        let equiDepth = Histogram(type: .equiDepth, buckets: buckets)
        let equiWidth = Histogram(type: .equiWidth, buckets: buckets)
        let maxDiff = Histogram(type: .maxDiff, buckets: buckets)
        let vOptimal = Histogram(type: .vOptimal, buckets: buckets)
        
        #expect(equiDepth.type == .equiDepth)
        #expect(equiWidth.type == .equiWidth)
        #expect(maxDiff.type == .maxDiff)
        #expect(vOptimal.type == .vOptimal)
    }
    
    @Test func testHistogramBucket() async throws {
        // Arrange
        let bucket = HistogramBucket(
            lowerBound: "1",
            upperBound: "10",
            rowCount: 100,
            distinctCount: 10
        )
        
        // Assert
        #expect(bucket.minValue == "1")
        #expect(bucket.maxValue == "10")
        #expect(bucket.frequency == 100)
        #expect(bucket.distinctValues == 10)
    }
    
    // MARK: - HyperLogLog Tests
    
    @Test func testHyperLogLogCreation() async throws {
        // Arrange
        let hll = HyperLogLogSketch(precision: 12)
        
        // Assert
        #expect(hll.precision == 12)
        #expect(hll.registers.count == 4096) // 2^12
        #expect(hll.estimatedCardinality == 0)
    }
    
    @Test func testHyperLogLogDefaultPrecision() async throws {
        // Arrange
        let hll = HyperLogLogSketch()
        
        // Assert
        #expect(hll.precision == 12)
        #expect(hll.registers.count == 4096)
    }
    
    @Test func testHyperLogLogAddValue() async throws {
        // Arrange
        var hll = HyperLogLogSketch(precision: 8)
        
        // Act
        hll.add(value: "test1")
        hll.add(value: "test2")
        hll.add(value: "test1") // Duplicate
        
        // Assert
        #expect(hll.estimatedCardinality >= 0)
        #expect(hll.estimatedCardinality <= 3)
    }
    
    @Test func testHyperLogLogEstimate() async throws {
        // Arrange
        var hll = HyperLogLogSketch(precision: 8)
        
        // Act
        for i in 0..<100 {
            hll.add(value: "value_\(i)")
        }
        
        let estimate = hll.estimate()
        
        // Assert
        #expect(estimate >= 0)
        #expect(estimate <= 100)
    }
    
    // MARK: - ANALYZE Operations Tests
    
    @Test func testStartAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await statsManager.startAnalyze(table: "test_table")
        
        // Assert
        // Should complete without error
    }
    
    @Test func testAnalyzeTable() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 100)
    }
    
    @Test func testAnalyzeEmptyTable() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows: [Row] = []
        
        // Act
        await statsManager.analyze(table: "empty_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("empty_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 0)
    }
    
    @Test func testAnalyzeTableWithColumns() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 50)
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 50)
        
        // Check column statistics
        let colStats = await statsManager.getColumnStatistics("test_table", column: "id")
        #expect(colStats != nil)
    }
    
    // MARK: - Incremental Updates Tests
    
    @Test func testRecordModification() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.recordModification(table: "test_table")
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        #expect(tableStats?.modifications == 1)
    }
    
    @Test func testUpdateRowCount() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.updateRowCount(table: "test_table", delta: 50)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        #expect(tableStats?.rowCount == 150)
    }
    
    @Test func testUpdateRowCountNegative() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        await statsManager.updateRowCount(table: "test_table", delta: -30)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("test_table")
        #expect(tableStats?.rowCount == 70)
    }
    
    // MARK: - Auto-Analyze Tests
    
    @Test func testShouldAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let shouldAnalyze = await statsManager.shouldAnalyze("test_table")
        
        // Assert
        #expect(shouldAnalyze == true) // Should be true for new table
    }
    
    @Test func testShouldAnalyzeAfterAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let shouldAnalyze = await statsManager.shouldAnalyze("test_table")
        
        // Assert
        #expect(shouldAnalyze == false) // Should be false after recent analyze
    }
    
    @Test func testSetAutoAnalyze() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await statsManager.setAutoAnalyze(enabled: false)
        
        // Assert
        // Should complete without error
    }
    
    // MARK: - Cardinality Estimation Tests
    
    @Test func testEstimateCardinality() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let cardinality = await statsManager.estimateCardinality(table: "test_table", predicate: "age > 18")
        
        // Assert
        #expect(cardinality >= 0)
        #expect(cardinality <= 1000)
    }
    
    @Test func testEstimateCardinalityDefault() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let cardinality = await statsManager.estimateCardinality(table: "non_existent", predicate: "age > 18")
        
        // Assert
        #expect(cardinality == 1000) // Default estimate
    }
    
    @Test func testEstimateSelectivity() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let selectivity = await statsManager.estimateSelectivity(table: "test_table", column: "id", predicate: "id = 1")
        
        // Assert
        #expect(selectivity >= 0.0)
        #expect(selectivity <= 1.0)
    }
    
    @Test func testEstimateSelectivityDefault() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let selectivity = await statsManager.estimateSelectivity(table: "non_existent", column: "id", predicate: "id = 1")
        
        // Assert
        #expect(selectivity == 0.1) // Default 10%
    }
    
    // MARK: - Query Methods Tests
    
    @Test func testGetTableStatistics() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let tableStats = await statsManager.getTableStatistics("test_table")
        
        // Assert
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 100)
    }
    
    @Test func testGetTableStatisticsNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let tableStats = await statsManager.getTableStatistics("non_existent")
        
        // Assert
        #expect(tableStats == nil)
    }
    
    @Test func testGetColumnStatistics() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let colStats = await statsManager.getColumnStatistics("test_table", column: "id")
        
        // Assert
        #expect(colStats != nil)
        #expect(colStats?.columnName == "id")
    }
    
    @Test func testGetColumnStatisticsNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let colStats = await statsManager.getColumnStatistics("non_existent", column: "id")
        
        // Assert
        #expect(colStats == nil)
    }
    
    @Test func testGetIndexStats() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let indexStats = await statsManager.getIndexStats(indexName: "test_index")
        
        // Assert
        #expect(indexStats == nil) // No index stats by default
    }
    
    @Test func testGetFreshnessScore() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Act
        let freshness = await statsManager.getFreshnessScore(table: "test_table")
        
        // Assert
        #expect(freshness >= 0.0)
        #expect(freshness <= 1.0)
    }
    
    @Test func testGetFreshnessScoreNonExistent() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        let freshness = await statsManager.getFreshnessScore(table: "non_existent")
        
        // Assert
        #expect(freshness == 0.0)
    }
    
    // MARK: - Performance Tests
    
    @Test func testAnalyzePerformance() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        
        let startTime = Date()
        
        // Act
        await statsManager.analyze(table: "test_table", rows: rows)
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        #expect(duration < 5.0) // Should complete in reasonable time
    }
    
    @Test func testBulkAnalyzeOperations() async throws {
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
        
        #expect(duration < 10.0) // Should complete in reasonable time
    }
    
    @Test func testConcurrentAnalyzeOperations() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<5 {
                group.addTask {
                    let rows = createTestRows(count: 100)
                    await statsManager.analyze(table: "concurrent_table_\(i)", rows: rows)
                }
            }
        }
        
        // Assert
        // Should complete without errors
    }
    
    // MARK: - Edge Cases Tests
    
    @Test func testAnalyzeWithEmptyRows() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows: [Row] = []
        
        // Act
        await statsManager.analyze(table: "empty_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("empty_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 0)
    }
    
    @Test func testAnalyzeWithSingleRow() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1)
        
        // Act
        await statsManager.analyze(table: "single_row_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("single_row_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 1)
    }
    
    @Test func testAnalyzeWithLargeDataset() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 10000)
        
        // Act
        await statsManager.analyze(table: "large_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("large_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 10000)
    }
    
    @Test func testAnalyzeWithNullValues() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRowsWithNulls(count: 100)
        
        // Act
        await statsManager.analyze(table: "nulls_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("nulls_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 100)
    }
    
    // MARK: - Integration Tests
    
    @Test func testCompleteStatisticsWorkflow() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 1000)
        
        // Act & Assert - Analyze
        await statsManager.analyze(table: "workflow_table", rows: rows)
        let tableStats = await statsManager.getTableStatistics("workflow_table")
        #expect(tableStats?.rowCount == 1000)
        
        // Act & Assert - Record modifications
        await statsManager.recordModification(table: "workflow_table")
        let modifiedStats = await statsManager.getTableStatistics("workflow_table")
        #expect(modifiedStats?.modifications == 1)
        
        // Act & Assert - Update row count
        await statsManager.updateRowCount(table: "workflow_table", delta: 100)
        let updatedStats = await statsManager.getTableStatistics("workflow_table")
        #expect(updatedStats?.rowCount == 1100)
        
        // Act & Assert - Estimate cardinality
        let cardinality = await statsManager.estimateCardinality(table: "workflow_table", predicate: "id > 500")
        #expect(cardinality >= 0)
        
        // Act & Assert - Estimate selectivity
        let selectivity = await statsManager.estimateSelectivity(table: "workflow_table", column: "id", predicate: "id = 1")
        #expect(selectivity >= 0.0)
        #expect(selectivity <= 1.0)
    }
    
    @Test func testStatisticsConsistency() async throws {
        // Arrange
        let statsManager = StatisticsMaintenanceManager()
        let rows = createTestRows(count: 100)
        
        // Act
        await statsManager.analyze(table: "consistency_table", rows: rows)
        
        // Assert
        let tableStats = await statsManager.getTableStatistics("consistency_table")
        #expect(tableStats != nil)
        #expect(tableStats?.rowCount == 100)
        #expect(tableStats?.pageCount > 0)
        #expect(tableStats?.avgRowSize > 0)
    }
    
    // MARK: - Helper Methods
    
    private func createTestRows(count: Int) -> [Row] {
        var rows: [Row] = []
        for i in 0..<count {
            let row = Row(values: [
                "id": .int(i),
                "name": .string("user_\(i)"),
                "age": .int(18 + (i % 50)),
                "email": .string("user\(i)@example.com")
            ])
            rows.append(row)
        }
        return rows
    }
    
    private func createTestRowsWithNulls(count: Int) -> [Row] {
        var rows: [Row] = []
        for i in 0..<count {
            let row = Row(values: [
                "id": .int(i),
                "name": i % 2 == 0 ? .string("user_\(i)") : .null,
                "age": i % 3 == 0 ? .null : .int(18 + (i % 50)),
                "email": .string("user\(i)@example.com")
            ])
            rows.append(row)
        }
        return rows
    }
}
