#!/usr/bin/env swift

import Foundation

// Coverage Guard Script for ColibrìDB
// Validates code coverage against defined targets

struct CoverageTargets: Codable {
    let global: GlobalTargets
    let modules: [String: ModuleTargets]
    let exclusions: Exclusions
    let reporting: Reporting
}

struct GlobalTargets: Codable {
    let minimum: Int
    let target: Int
    let excellent: Int
}

struct ModuleTargets: Codable {
    let minimum: Int
    let target: Int
    let rationale: String?
    let files: [String]?
}

struct Exclusions: Codable {
    let files: [String]
    let patterns: [String]
}

struct Reporting: Codable {
    let format: String
    let html_report: Bool
    let fail_under_global: Bool
    let fail_under_module: Bool
}

struct CoverageData: Codable {
    let data: [CoverageFile]
}

struct CoverageFile: Codable {
    let files: [FileCoverage]
}

struct FileCoverage: Codable {
    let filename: String
    let summary: CoverageSummary
}

struct CoverageSummary: Codable {
    let lines: CoverageMetrics
    let functions: CoverageMetrics
    let branches: CoverageMetrics
}

struct CoverageMetrics: Codable {
    let count: Int
    let covered: Int
    let percent: Double
}

func main() {
    guard CommandLine.arguments.count >= 3 else {
        print("Usage: coverage_guard.swift <coverage.json> <targets.json>")
        exit(1)
    }
    
    let coverageFile = CommandLine.arguments[1]
    let targetsFile = CommandLine.arguments[2]
    
    do {
        // Load coverage data
        let coverageData = try loadCoverageData(from: coverageFile)
        
        // Load targets
        let targets = try loadTargets(from: targetsFile)
        
        // Validate coverage
        let result = validateCoverage(coverageData: coverageData, targets: targets)
        
        // Print results
        printCoverageReport(result: result)
        
        // Exit with appropriate code
        exit(result.failed ? 1 : 0)
        
    } catch {
        print("Error: \(error)")
        exit(1)
    }
}

func loadCoverageData(from file: String) throws -> CoverageData {
    let data = try Data(contentsOf: URL(fileURLWithPath: file))
    return try JSONDecoder().decode(CoverageData.self, from: data)
}

func loadTargets(from file: String) throws -> CoverageTargets {
    let data = try Data(contentsOf: URL(fileURLWithPath: file))
    return try JSONDecoder().decode(CoverageTargets.self, from: data)
}

struct CoverageResult {
    let globalCoverage: Double
    let moduleResults: [String: ModuleResult]
    let failed: Bool
}

struct ModuleResult {
    let coverage: Double
    let target: Int
    let minimum: Int
    let passed: Bool
    let files: [String]
}

func validateCoverage(coverageData: CoverageData, targets: CoverageTargets) -> CoverageResult {
    var moduleResults: [String: ModuleResult] = [:]
    var totalLines = 0
    var coveredLines = 0
    var failed = false
    
    // Calculate global coverage
    for file in coverageData.data.flatMap({ $0.files }) {
        totalLines += file.summary.lines.count
        coveredLines += file.summary.lines.covered
    }
    
    let globalCoverage = totalLines > 0 ? Double(coveredLines) / Double(totalLines) * 100 : 0
    
    // Check global coverage
    if globalCoverage < Double(targets.global.minimum) {
        failed = true
    }
    
    // Check module-specific coverage
    for (moduleName, moduleTargets) in targets.modules {
        let moduleFiles = moduleTargets.files ?? []
        var moduleLines = 0
        var moduleCovered = 0
        
        for file in coverageData.data.flatMap({ $0.files }) {
            if isFileInModule(file.filename, moduleFiles: moduleFiles) {
                moduleLines += file.summary.lines.count
                moduleCovered += file.summary.lines.covered
            }
        }
        
        let moduleCoverage = moduleLines > 0 ? Double(moduleCovered) / Double(moduleLines) * 100 : 0
        let passed = moduleCoverage >= Double(moduleTargets.minimum)
        
        if !passed {
            failed = true
        }
        
        moduleResults[moduleName] = ModuleResult(
            coverage: moduleCoverage,
            target: moduleTargets.target,
            minimum: moduleTargets.minimum,
            passed: passed,
            files: moduleFiles
        )
    }
    
    return CoverageResult(
        globalCoverage: globalCoverage,
        moduleResults: moduleResults,
        failed: failed
    )
}

func isFileInModule(_ filename: String, moduleFiles: [String]) -> Bool {
    for pattern in moduleFiles {
        if filename.contains(pattern) {
            return true
        }
    }
    return false
}

func printCoverageReport(result: CoverageResult) {
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print("📊 COVERAGE QUALITY GATE REPORT")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print("")
    
    print("🌍 Global Coverage: \(String(format: "%.1f", result.globalCoverage))%")
    print("")
    
    print("📋 Module Coverage:")
    for (moduleName, moduleResult) in result.moduleResults.sorted(by: { $0.key < $1.key }) {
        let status = moduleResult.passed ? "✅" : "❌"
        print("  \(status) \(moduleName): \(String(format: "%.1f", moduleResult.coverage))% (min: \(moduleResult.minimum)%, target: \(moduleResult.target)%)")
    }
    
    print("")
    if result.failed {
        print("❌ Coverage quality gate FAILED")
        print("   Some modules do not meet minimum coverage requirements")
    } else {
        print("✅ Coverage quality gate PASSED")
        print("   All modules meet minimum coverage requirements")
    }
    print("")
}

main()