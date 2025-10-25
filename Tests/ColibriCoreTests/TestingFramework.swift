//
//  TestingFramework.swift
//

import Foundation

public protocol Testable {
    func checkInvariants() -> Bool
    func getState() -> [String: Any]
}

public struct TestCase {
    public let name: String
    public let setup: () async throws -> Void
    public let execute: () async throws -> Void
    public let teardown: () async throws -> Void
    public let expectedResult: Bool
    
    public init(
        name: String,
        setup: @escaping () async throws -> Void = {},
        execute: @escaping () async throws -> Void,
        teardown: @escaping () async throws -> Void = {},
        expectedResult: Bool = true
    ) {
        self.name = name
        self.setup = setup
        self.execute = execute
        self.teardown = teardown
        self.expectedResult = expectedResult
    }
}

public actor TestRunner {
    private var results: [TestResult] = []
    
    public init() {}
    
    public func run(_ testCase: TestCase) async -> TestResult {
        let startTime = Date()
        
        do {
            try await testCase.setup()
            try await testCase.execute()
            try await testCase.teardown()
            
            let duration = Date().timeIntervalSince(startTime)
            let result = TestResult(
                name: testCase.name,
                passed: true,
                duration: duration,
                error: nil
            )
            results.append(result)
            return result
            
        } catch {
            let duration = Date().timeIntervalSince(startTime)
            let result = TestResult(
                name: testCase.name,
                passed: false,
                duration: duration,
                error: error
            )
            results.append(result)
            return result
        }
    }
    
    public func getResults() -> [TestResult] {
        return results
    }
    
    public func getSummary() -> TestSummary {
        let passed = results.filter { $0.passed }.count
        let failed = results.count - passed
        let totalDuration = results.reduce(0.0) { $0 + $1.duration }
        
        return TestSummary(
            total: results.count,
            passed: passed,
            failed: failed,
            duration: totalDuration
        )
    }
}

public struct TestResult {
    public let name: String
    public let passed: Bool
    public let duration: TimeInterval
    public let error: Error?
}

public struct TestSummary {
    public let total: Int
    public let passed: Int
    public let failed: Int
    public let duration: TimeInterval
}

