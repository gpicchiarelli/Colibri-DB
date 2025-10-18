#!/usr/bin/env swift
/*
 Coverage Guard for ColibrìDB
 Validates code coverage against module-specific targets.
 
 Usage:
   swift coverage_guard.swift <coverage.json> <targets.json>
 
 Exit codes:
   0 - All coverage targets met
   1 - Coverage below targets
   2 - Error in execution
*/

import Foundation

// MARK: - Models

struct CoverageData: Codable {
    let data: [CoverageFile]
}

struct CoverageFile: Codable {
    let filename: String
    let summary: CoverageSummary
}

struct CoverageSummary: Codable {
    let lines: CoverageMetric
    let functions: CoverageMetric
    let regions: CoverageMetric?
}

struct CoverageMetric: Codable {
    let count: Int
    let covered: Int
    let percent: Double
}

struct CoverageTargets: Codable {
    let global: GlobalTarget
    let modules: [String: ModuleTarget]
    let exclusions: Exclusions?
}

struct GlobalTarget: Codable {
    let minimum: Double
    let target: Double
}

struct ModuleTarget: Codable {
    let minimum: Double
    let target: Double
    let rationale: String
    let files: [String]
}

struct Exclusions: Codable {
    let files: [String]
    let patterns: [String]
}

// MARK: - Colors

enum Color: String {
    case reset = "\u{001B}[0m"
    case red = "\u{001B}[91m"
    case green = "\u{001B}[92m"
    case yellow = "\u{001B}[93m"
    case blue = "\u{001B}[94m"
    case bold = "\u{001B}[1m"
    
    func wrap(_ text: String) -> String {
        return "\(rawValue)\(text)\(Color.reset.rawValue)"
    }
}

// MARK: - Coverage Guard

class CoverageGuard {
    let coverageFile: String
    let targetsFile: String
    
    var coverage: CoverageData?
    var targets: CoverageTargets?
    
    var failures: [(module: String, target: Double, actual: Double, files: [String])] = []
    var warnings: [(module: String, target: Double, actual: Double)] = []
    var passes: [(module: String, actual: Double)] = []
    
    init(coverageFile: String, targetsFile: String) {
        self.coverageFile = coverageFile
        self.targetsFile = targetsFile
    }
    
    func loadData() -> Bool {
        // Load targets
        guard let targetsURL = URL(string: "file://\(targetsFile)"),
              let targetsData = try? Data(contentsOf: targetsURL),
              let loadedTargets = try? JSONDecoder().decode(CoverageTargets.self, from: targetsData) else {
            print(Color.red.wrap("✗ Failed to load targets: \(targetsFile)"))
            return false
        }
        self.targets = loadedTargets
        print(Color.green.wrap("✓") + " Loaded targets: \(targetsFile)")
        
        // Load coverage
        guard let coverageURL = URL(string: "file://\(coverageFile)"),
              let coverageData = try? Data(contentsOf: coverageURL),
              let loadedCoverage = try? JSONDecoder().decode(CoverageData.self, from: coverageData) else {
            print(Color.red.wrap("✗ Failed to load coverage: \(coverageFile)"))
            return false
        }
        self.coverage = loadedCoverage
        print(Color.green.wrap("✓") + " Loaded coverage: \(coverageFile)")
        
        return true
    }
    
    func isFileExcluded(_ filename: String) -> Bool {
        guard let exclusions = targets?.exclusions else { return false }
        
        // Check exact file matches
        for excluded in exclusions.files {
            if filename.contains(excluded) {
                return true
            }
        }
        
        // Check patterns
        for pattern in exclusions.patterns {
            let regexPattern = pattern
                .replacingOccurrences(of: "**", with: ".*")
                .replacingOccurrences(of: "*", with: "[^/]*")
            
            if let regex = try? NSRegularExpression(pattern: regexPattern),
               regex.firstMatch(in: filename, range: NSRange(filename.startIndex..., in: filename)) != nil {
                return true
            }
        }
        
        return false
    }
    
    func getModuleCoverage(moduleName: String, moduleTarget: ModuleTarget) -> Double? {
        guard let coverage = coverage else { return nil }
        
        var totalLines = 0
        var coveredLines = 0
        var fileCount = 0
        
        for file in coverage.data {
            guard !isFileExcluded(file.filename) else { continue }
            
            // Check if file belongs to this module
            let belongsToModule = moduleTarget.files.contains { pattern in
                file.filename.contains(pattern.replacingOccurrences(of: "*.swift", with: ""))
            }
            
            if belongsToModule {
                totalLines += file.summary.lines.count
                coveredLines += file.summary.lines.covered
                fileCount += 1
            }
        }
        
        guard totalLines > 0 else { return nil }
        return (Double(coveredLines) / Double(totalLines)) * 100.0
    }
    
    func validate() -> Bool {
        guard let targets = targets else { return false }
        
        print("\n" + Color.bold.wrap("Running Coverage Validation...") + "\n")
        
        var allPassed = true
        
        for (moduleName, moduleTarget) in targets.modules {
            guard let actualCoverage = getModuleCoverage(moduleName: moduleName, moduleTarget: moduleTarget) else {
                warnings.append((module: moduleName, target: moduleTarget.minimum, actual: 0.0))
                continue
            }
            
            if actualCoverage < moduleTarget.minimum {
                failures.append((
                    module: moduleName,
                    target: moduleTarget.minimum,
                    actual: actualCoverage,
                    files: moduleTarget.files
                ))
                allPassed = false
            } else if actualCoverage < moduleTarget.target {
                warnings.append((
                    module: moduleName,
                    target: moduleTarget.target,
                    actual: actualCoverage
                ))
            } else {
                passes.append((module: moduleName, actual: actualCoverage))
            }
        }
        
        return allPassed
    }
    
    func printReport() {
        print("\n" + String(repeating: "=", count: 80))
        print(Color.bold.wrap("Coverage Guard Report"))
        print(String(repeating: "=", count: 80) + "\n")
        
        // Failures
        if !failures.isEmpty {
            print(Color.red.wrap(Color.bold.wrap("✗ FAILURES (\(failures.count))")))
            print(Color.red.wrap("Coverage below minimum targets:") + "\n")
            
            for failure in failures {
                print("  " + Color.red.wrap("✗") + " " + Color.bold.wrap(failure.module))
                print("    Minimum: \(String(format: "%.1f", failure.target))%")
                print("    Actual:  " + Color.red.wrap(String(format: "%.1f", failure.actual) + "%"))
                print("    Gap:     " + Color.red.wrap(String(format: "%.1f", failure.target - failure.actual) + "%"))
                print("    Files:   \(failure.files.joined(separator: ", "))")
                print()
            }
        }
        
        // Warnings
        if !warnings.isEmpty {
            print(Color.yellow.wrap(Color.bold.wrap("⚠ WARNINGS (\(warnings.count))")))
            print(Color.yellow.wrap("Coverage below target but above minimum:") + "\n")
            
            for warning in warnings {
                print("  " + Color.yellow.wrap("⚠") + " " + warning.module)
                print("    Target: \(String(format: "%.1f", warning.target))%")
                print("    Actual: " + Color.yellow.wrap(String(format: "%.1f", warning.actual) + "%"))
                print()
            }
        }
        
        // Passes
        if !passes.isEmpty {
            print(Color.green.wrap(Color.bold.wrap("✓ PASSED (\(passes.count))")))
            print(Color.green.wrap("Coverage meets or exceeds targets:") + "\n")
            
            for pass in passes.prefix(5) {
                print("  " + Color.green.wrap("✓") + " " + pass.module)
                print("    Coverage: " + Color.green.wrap(String(format: "%.1f", pass.actual) + "%"))
                print()
            }
            
            if passes.count > 5 {
                print("  ... and \(passes.count - 5) more modules\n")
            }
        }
        
        // Summary
        print(String(repeating: "=", count: 80))
        print(Color.bold.wrap("Summary:"))
        let total = failures.count + warnings.count + passes.count
        print("  Total modules checked: \(total)")
        print("  " + Color.green.wrap("Passed: \(passes.count)"))
        print("  " + Color.yellow.wrap("Warnings: \(warnings.count)"))
        print("  " + Color.red.wrap("Failures: \(failures.count)"))
        print(String(repeating: "=", count: 80) + "\n")
    }
    
    func run() -> Int32 {
        guard loadData() else {
            return 2
        }
        
        let isValid = validate()
        printReport()
        
        if isValid {
            print(Color.green.wrap(Color.bold.wrap("✓ Coverage guard PASSED")))
            return 0
        } else {
            print(Color.red.wrap(Color.bold.wrap("✗ Coverage guard FAILED")))
            print(Color.red.wrap("Coverage is below minimum targets."))
            print(Color.red.wrap("Please add tests to improve coverage before merging."))
            return 1
        }
    }
}

// MARK: - Main

guard CommandLine.arguments.count == 3 else {
    print("Usage: swift coverage_guard.swift <coverage.json> <targets.json>")
    print("\nExample:")
    print("  swift coverage_guard.swift .build/coverage.json rules/coverage_targets.json")
    exit(2)
}

let coverageFile = CommandLine.arguments[1]
let targetsFile = CommandLine.arguments[2]

let guard = CoverageGuard(coverageFile: coverageFile, targetsFile: targetsFile)
let exitCode = guard.run()
exit(exitCode)

