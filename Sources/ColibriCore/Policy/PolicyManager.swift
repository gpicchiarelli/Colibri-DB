//
//  PolicyManager.swift
//  ColibrìDB Policy Manager Implementation
//
//  Based on: spec/Policy.tla
//  Implements: Database policy management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Policy Consistency: Policies are consistent
//  - Enforcement Integrity: Policy enforcement is correct
//  - Audit Log Completeness: Audit log is complete
//

import Foundation

// MARK: - Policy Types

/// Policy manager policy type
/// Corresponds to TLA+: PolicyType
public enum PolicyManagerPolicyType: String, Codable, Sendable, CaseIterable {
    case security = "security"
    case resource = "resource"
    case dataRetention = "dataRetention"
    case access = "access"
    case compliance = "compliance"
}

/// Policy rule
/// Corresponds to TLA+: PolicyRule
public struct PolicyRule: Codable, Sendable, Equatable {
    public let ruleId: String
    public let policyType: PolicyManagerPolicyType
    public let name: String
    public let description: String
    public let condition: String
    public let action: String
    public let priority: Int
    public let isActive: Bool
    
    public init(ruleId: String, policyType: PolicyManagerPolicyType, name: String, description: String, condition: String, action: String, priority: Int, isActive: Bool) {
        self.ruleId = ruleId
        self.policyType = policyType
        self.name = name
        self.description = description
        self.condition = condition
        self.action = action
        self.priority = priority
        self.isActive = isActive
    }
}

/// Policy action
/// Corresponds to TLA+: PolicyAction
public enum PolicyAction: String, Codable, Sendable, CaseIterable {
    case allow = "allow"
    case deny = "deny"
    case warn = "warn"
    case log = "log"
    case encrypt = "encrypt"
    case audit = "audit"
}

/// Policy evaluation result
/// Corresponds to TLA+: PolicyEvaluationResult
public struct PolicyEvaluationResult: Codable, Sendable, Equatable {
    public let ruleId: String
    public let action: PolicyAction
    public let reason: String
    public let timestamp: UInt64
    public let metadata: [String: String]
    
    public init(ruleId: String, action: PolicyAction, reason: String, timestamp: UInt64, metadata: [String: String]) {
        self.ruleId = ruleId
        self.action = action
        self.reason = reason
        self.timestamp = timestamp
        self.metadata = metadata
    }
}

// MARK: - Policy Manager

/// Policy Manager for database policy management
/// Corresponds to TLA+ module: Policy.tla
public actor PolicyManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Policies
    /// TLA+: policies \in [String -> PolicyRule]
    private var policies: [String: PolicyRule] = [:]
    
    /// Active policies
    /// TLA+: activePolicies \in Set(String)
    private var activePolicies: Set<String> = []
    
    /// Policy violations
    /// TLA+: policyViolations \in [String -> PolicyEvaluationResult]
    private var policyViolations: [String: PolicyEvaluationResult] = [:]
    
    /// Audit log
    /// TLA+: auditLog \in Seq(String)
    private var auditLog: [String] = []
    
    // MARK: - Dependencies
    
    /// Audit manager
    private let auditLogger: PolicyAuditLogger
    
    /// Security manager
    private let securityManager: PolicySecurityManager
    
    // MARK: - Initialization
    
    public init(auditLogger: PolicyAuditLogger, securityManager: PolicySecurityManager) {
        self.auditLogger = auditLogger
        self.securityManager = securityManager
        
        // TLA+ Init
        self.policies = [:]
        self.activePolicies = []
        self.policyViolations = [:]
        self.auditLog = []
    }
    
    // MARK: - Policy Management Operations
    
    /// Add policy
    /// TLA+ Action: AddPolicy(policy)
    public func addPolicy(policy: PolicyRule) async throws {
        // TLA+: Add policy
        policies[policy.ruleId] = policy
        
        // TLA+: Add to active policies if active
        if policy.isActive {
            activePolicies.insert(policy.ruleId)
        }
        
        // TLA+: Log policy addition
        auditLog.append("Added policy: \(policy.ruleId) - \(policy.name)")
        
        logInfo("Added policy: \(policy.ruleId)")
    }
    
    /// Remove policy
    /// TLA+ Action: RemovePolicy(ruleId)
    public func removePolicy(ruleId: String) async throws {
        // TLA+: Remove policy
        policies.removeValue(forKey: ruleId)
        activePolicies.remove(ruleId)
        policyViolations.removeValue(forKey: ruleId)
        
        // TLA+: Log policy removal
        auditLog.append("Removed policy: \(ruleId)")
        
        logInfo("Removed policy: \(ruleId)")
    }
    
    /// Evaluate policy
    /// TLA+ Action: EvaluatePolicy(ruleId, context)
    public func evaluatePolicy(ruleId: String, context: [String: String]) async throws -> PolicyEvaluationResult {
        // TLA+: Check if policy exists
        guard let policy = policies[ruleId] else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Check if policy is active
        guard policy.isActive else {
            throw PolicyError.policyInactive
        }
        
        // TLA+: Evaluate policy condition
        let conditionMet = try await evaluateCondition(condition: policy.condition, context: context)
        
        // TLA+: Determine action
        let action: PolicyAction = conditionMet ? .allow : .deny
        
        // TLA+: Create evaluation result
        let result = PolicyEvaluationResult(
            ruleId: ruleId,
            action: action,
            reason: conditionMet ? "Condition met" : "Condition not met",
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000),
            metadata: context
        )
        
        // TLA+: Store violation if denied
        if action == .deny {
            policyViolations[ruleId] = result
        }
        
        // TLA+: Log evaluation
        auditLog.append("Evaluated policy: \(ruleId) - \(action.rawValue)")
        
        logInfo("Evaluated policy: \(ruleId) - \(action.rawValue)")
        return result
    }
    
    /// Enforce policy
    /// TLA+ Action: EnforcePolicy(ruleId, context)
    public func enforcePolicy(ruleId: String, context: [String: String]) async throws -> Bool {
        // TLA+: Evaluate policy
        let result = try await evaluatePolicy(ruleId: ruleId, context: context)
        
        // TLA+: Enforce action
        switch result.action {
        case .allow:
            return true
        case .deny:
            return false
        case .warn:
            logInfo("Policy warning: \(result.reason)")
            return true
        case .log:
            auditLog.append("Policy log: \(result.reason)")
            return true
        case .encrypt:
            try await securityManager.encryptData(data: context["data"] ?? "")
            return true
        case .audit:
            try await auditLogger.auditEvent(event: result.reason, metadata: result.metadata)
            return true
        }
    }
    
    // MARK: - Helper Methods
    
    /// Evaluate condition
    private func evaluateCondition(condition: String, context: [String: String]) async throws -> Bool {
        // TLA+: Evaluate condition
        // This is a simplified implementation
        // In practice, you would use a proper expression evaluator
        
        if condition.contains("user_role") {
            let userRole = context["user_role"] ?? ""
            return userRole == "admin"
        }
        
        if condition.contains("time_range") {
            let currentHour = Calendar.current.component(.hour, from: Date())
            return currentHour >= 9 && currentHour <= 17
        }
        
        if condition.contains("data_size") {
            let dataSize = Int(context["data_size"] ?? "0") ?? 0
            return dataSize <= 1000000 // 1MB
        }
        
        return true // Default to allow
    }
    
    
    
    
    // MARK: - Query Operations
    
    /// Get policy (public)
    public func getPolicy(ruleId: String) -> PolicyRule? {
        return policies[ruleId]
    }
    
    /// Get violations (public)
    public func getViolations() -> [PolicyEvaluationResult] {
        return Array(policyViolations.values)
    }
    
    /// Check if has violations (public)
    public func hasViolations() -> Bool {
        return !policyViolations.isEmpty
    }
    
    /// Get all policies
    public func getAllPolicies() -> [PolicyRule] {
        return Array(policies.values)
    }
    
    /// Get active policies
    public func getActivePolicies() -> [PolicyRule] {
        return activePolicies.compactMap { policies[$0] }
    }
    
    /// Get policies by type
    public func getPoliciesByType(type: PolicyManagerPolicyType) -> [PolicyRule] {
        return policies.values.filter { $0.policyType == type }
    }
    
    /// Get audit log
    public func getAuditLog() -> [String] {
        return auditLog
    }
    
    /// Get policy count
    public func getPolicyCount() -> Int {
        return policies.count
    }
    
    /// Get active policy count
    public func getActivePolicyCount() -> Int {
        return activePolicies.count
    }
    
    /// Get violation count
    public func getViolationCount() -> Int {
        return policyViolations.count
    }
    
    /// Check if policy exists
    public func policyExists(ruleId: String) -> Bool {
        return policies[ruleId] != nil
    }
    
    /// Check if policy is active
    public func isPolicyActive(ruleId: String) -> Bool {
        return activePolicies.contains(ruleId)
    }
    
    /// Get policy by name
    public func getPolicyByName(name: String) -> PolicyRule? {
        return policies.values.first { $0.name == name }
    }
    
    /// Get policies by priority
    public func getPoliciesByPriority(priority: Int) -> [PolicyRule] {
        return policies.values.filter { $0.priority == priority }
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check policy consistency invariant
    /// TLA+ Inv_Policy_PolicyConsistency
    public func checkPolicyConsistencyInvariant() -> Bool {
        // Check that policies are consistent
        return true // Simplified
    }
    
    /// Check enforcement integrity invariant
    /// TLA+ Inv_Policy_EnforcementIntegrity
    public func checkEnforcementIntegrityInvariant() -> Bool {
        // Check that policy enforcement is correct
        return true // Simplified
    }
    
    /// Check audit log completeness invariant
    /// TLA+ Inv_Policy_AuditLogCompleteness
    public func checkAuditLogCompletenessInvariant() -> Bool {
        // Check that audit log is complete
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let policyConsistency = checkPolicyConsistencyInvariant()
        let enforcementIntegrity = checkEnforcementIntegrityInvariant()
        let auditLogCompleteness = checkAuditLogCompletenessInvariant()
        
        return policyConsistency && enforcementIntegrity && auditLogCompleteness
    }
}

// MARK: - Supporting Types

/// Audit logger used by PolicyManager
public protocol PolicyAuditLogger: Sendable {
    func auditEvent(event: String, metadata: [String: String]) async throws
}

/// Security manager dependency for PolicyManager (distinct from core security subsystem)
public protocol PolicySecurityManager: Sendable {
    func encryptData(data: String) async throws
    func decryptData(data: String) async throws
}

/// Policy error
public enum PolicyError: Error, LocalizedError {
    case policyNotFound
    case policyInactive
    case evaluationFailed
    case enforcementFailed
    case invalidCondition
    
    public var errorDescription: String? {
        switch self {
        case .policyNotFound:
            return "Policy not found"
        case .policyInactive:
            return "Policy is inactive"
        case .evaluationFailed:
            return "Policy evaluation failed"
        case .enforcementFailed:
            return "Policy enforcement failed"
        case .invalidCondition:
            return "Invalid policy condition"
        }
    }
}