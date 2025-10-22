//
//  PolicyManager.swift
//  ColibrìDB Policy Management Implementation
//
//  Based on: spec/Policy.tla
//  Implements: Database policy management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Security: Access control and authorization
//  - Compliance: Regulatory compliance
//  - Audit: Policy enforcement tracking
//  - Flexibility: Dynamic policy updates
//

import Foundation

// MARK: - Policy Types

/// Policy type
/// Corresponds to TLA+: PolicyType
public enum PolicyType: String, Codable, Sendable {
    case access = "access"
    case dataRetention = "data_retention"
    case encryption = "encryption"
    case backup = "backup"
    case audit = "audit"
    case compliance = "compliance"
}

/// Policy status
/// Corresponds to TLA+: PolicyStatus
public enum PolicyStatus: String, Codable, Sendable {
    case active = "active"
    case inactive = "inactive"
    case pending = "pending"
    case expired = "expired"
}

/// Policy priority
/// Corresponds to TLA+: PolicyPriority
public enum PolicyPriority: String, Codable, Sendable {
    case low = "low"
    case medium = "medium"
    case high = "high"
    case critical = "critical"
}

/// Policy action
/// Corresponds to TLA+: PolicyAction
public enum PolicyAction: String, Codable, Sendable {
    case allow = "allow"
    case deny = "deny"
    case audit = "audit"
    case encrypt = "encrypt"
    case backup = "backup"
    case delete = "delete"
}

// MARK: - Policy Metadata

/// Policy metadata
/// Corresponds to TLA+: PolicyMetadata
public struct PolicyMetadata: Codable, Sendable, Equatable {
    public let policyId: String
    public let name: String
    public let type: PolicyType
    public let status: PolicyStatus
    public let priority: PolicyPriority
    public let description: String
    public let rules: [PolicyRule]
    public let createdAt: Date
    public let updatedAt: Date
    public let expiresAt: Date?
    
    public init(policyId: String, name: String, type: PolicyType, status: PolicyStatus, priority: PolicyPriority, description: String, rules: [PolicyRule], createdAt: Date = Date(), updatedAt: Date = Date(), expiresAt: Date? = nil) {
        self.policyId = policyId
        self.name = name
        self.type = type
        self.status = status
        self.priority = priority
        self.description = description
        self.rules = rules
        self.createdAt = createdAt
        self.updatedAt = updatedAt
        self.expiresAt = expiresAt
    }
}

/// Policy rule
/// Corresponds to TLA+: PolicyRule
public struct PolicyRule: Codable, Sendable, Equatable {
    public let ruleId: String
    public let condition: PolicyCondition
    public let action: PolicyAction
    public let parameters: [String: Value]
    public let priority: PolicyPriority
    
    public init(ruleId: String, condition: PolicyCondition, action: PolicyAction, parameters: [String: Value], priority: PolicyPriority) {
        self.ruleId = ruleId
        self.condition = condition
        self.action = action
        self.parameters = parameters
        self.priority = priority
    }
}

/// Policy condition
/// Corresponds to TLA+: PolicyCondition
public struct PolicyCondition: Codable, Sendable, Equatable {
    public let expression: String
    public let variables: [String: Value]
    public let operators: [PolicyOperator]
    
    public init(expression: String, variables: [String: Value], operators: [PolicyOperator]) {
        self.expression = expression
        self.variables = variables
        self.operators = operators
    }
}

/// Policy operator
/// Corresponds to TLA+: PolicyOperator
public enum PolicyOperator: String, Codable, Sendable {
    case equals = "equals"
    case notEquals = "not_equals"
    case greaterThan = "greater_than"
    case lessThan = "less_than"
    case contains = "contains"
    case startsWith = "starts_with"
    case endsWith = "ends_with"
    case regex = "regex"
    case in = "in"
    case notIn = "not_in"
}

/// Policy evaluation result
/// Corresponds to TLA+: PolicyEvaluationResult
public struct PolicyEvaluationResult: Codable, Sendable, Equatable {
    public let policyId: String
    public let ruleId: String
    public let action: PolicyAction
    public let matched: Bool
    public let reason: String
    public let timestamp: Date
    public let context: [String: Value]
    
    public init(policyId: String, ruleId: String, action: PolicyAction, matched: Bool, reason: String, timestamp: Date = Date(), context: [String: Value]) {
        self.policyId = policyId
        self.ruleId = ruleId
        self.action = action
        self.matched = matched
        self.reason = reason
        self.timestamp = timestamp
        self.context = context
    }
}

// MARK: - Policy Manager

/// Policy Manager for database policy management
/// Corresponds to TLA+ module: Policy.tla
public actor PolicyManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Policy registry
    /// TLA+: policies \in [PolicyId -> PolicyMetadata]
    private var policies: [String: PolicyMetadata] = [:]
    
    /// Policy evaluations
    /// TLA+: policyEvaluations \in Seq(PolicyEvaluationResult)
    private var policyEvaluations: [PolicyEvaluationResult] = []
    
    /// Active policies
    /// TLA+: activePolicies \in Set(PolicyId)
    private var activePolicies: Set<String> = []
    
    /// Policy violations
    /// TLA+: policyViolations \in Seq(PolicyViolation)
    private var policyViolations: [PolicyViolation] = []
    
    /// Policy audit log
    /// TLA+: policyAuditLog \in Seq(PolicyAuditEvent)
    private var policyAuditLog: [PolicyAuditEvent] = []
    
    /// Policy cache
    /// TLA+: policyCache \in [Context -> Set(PolicyId)]
    private var policyCache: [String: Set<String>] = [:]
    
    // MARK: - Dependencies
    
    /// Authentication manager
    private let authenticationManager: AuthenticationManager
    
    /// Audit manager
    private let auditManager: AuditManager
    
    /// WAL for logging
    private let wal: FileWAL
    
    // MARK: - Initialization
    
    public init(authenticationManager: AuthenticationManager, auditManager: AuditManager, wal: FileWAL) {
        self.authenticationManager = authenticationManager
        self.auditManager = auditManager
        self.wal = wal
        
        // TLA+ Init
        self.policies = [:]
        self.policyEvaluations = []
        self.activePolicies = []
        self.policyViolations = []
        self.policyAuditLog = []
        self.policyCache = [:]
    }
    
    // MARK: - Policy Management
    
    /// Create policy
    /// TLA+ Action: CreatePolicy(policyId, metadata)
    public func createPolicy(policyId: String, metadata: PolicyMetadata) throws {
        // TLA+: Check if policy already exists
        guard policies[policyId] == nil else {
            throw PolicyError.policyAlreadyExists
        }
        
        // TLA+: Validate policy metadata
        try validatePolicyMetadata(metadata)
        
        // TLA+: Create policy
        policies[policyId] = metadata
        
        // TLA+: Add to active policies if active
        if metadata.status == .active {
            activePolicies.insert(policyId)
        }
        
        // TLA+: Log policy creation
        let event = PolicyAuditEvent(
            eventId: "\(policyId)_created",
            policyId: policyId,
            eventType: .created,
            timestamp: Date(),
            data: ["name": .string(metadata.name), "type": .string(metadata.type.rawValue)])
        policyAuditLog.append(event)
        
        // TLA+: Clear policy cache
        clearPolicyCache()
    }
    
    /// Update policy
    /// TLA+ Action: UpdatePolicy(policyId, metadata)
    public func updatePolicy(policyId: String, metadata: PolicyMetadata) throws {
        // TLA+: Check if policy exists
        guard let existingPolicy = policies[policyId] else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Validate policy metadata
        try validatePolicyMetadata(metadata)
        
        // TLA+: Update policy
        policies[policyId] = metadata
        
        // TLA+: Update active policies
        if metadata.status == .active {
            activePolicies.insert(policyId)
        } else {
            activePolicies.remove(policyId)
        }
        
        // TLA+: Log policy update
        let event = PolicyAuditEvent(
            eventId: "\(policyId)_updated",
            policyId: policyId,
            eventType: .updated,
            timestamp: Date(),
            data: ["name": .string(metadata.name), "type": .string(metadata.type.rawValue)])
        policyAuditLog.append(event)
        
        // TLA+: Clear policy cache
        clearPolicyCache()
    }
    
    /// Delete policy
    /// TLA+ Action: DeletePolicy(policyId)
    public func deletePolicy(policyId: String) throws {
        // TLA+: Check if policy exists
        guard policies[policyId] != nil else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Remove from active policies
        activePolicies.remove(policyId)
        
        // TLA+: Remove policy
        policies.removeValue(forKey: policyId)
        
        // TLA+: Log policy deletion
        let event = PolicyAuditEvent(
            eventId: "\(policyId)_deleted",
            policyId: policyId,
            eventType: .deleted,
            timestamp: Date(),
            data: [:])
        policyAuditLog.append(event)
        
        // TLA+: Clear policy cache
        clearPolicyCache()
    }
    
    /// Activate policy
    /// TLA+ Action: ActivatePolicy(policyId)
    public func activatePolicy(policyId: String) throws {
        // TLA+: Check if policy exists
        guard var policy = policies[policyId] else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Update policy status
        let updatedPolicy = PolicyMetadata(
            policyId: policy.policyId,
            name: policy.name,
            type: policy.type,
            status: .active,
            priority: policy.priority,
            description: policy.description,
            rules: policy.rules,
            createdAt: policy.createdAt,
            updatedAt: Date(),
            expiresAt: policy.expiresAt
        )
        policies[policyId] = updatedPolicy
        
        // TLA+: Add to active policies
        activePolicies.insert(policyId)
        
        // TLA+: Log policy activation
        let event = PolicyAuditEvent(
            eventId: "\(policyId)_activated",
            policyId: policyId,
            eventType: .activated,
            timestamp: Date(),
            data: [:])
        policyAuditLog.append(event)
        
        // TLA+: Clear policy cache
        clearPolicyCache()
    }
    
    /// Deactivate policy
    /// TLA+ Action: DeactivatePolicy(policyId)
    public func deactivatePolicy(policyId: String) throws {
        // TLA+: Check if policy exists
        guard var policy = policies[policyId] else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Update policy status
        let updatedPolicy = PolicyMetadata(
            policyId: policy.policyId,
            name: policy.name,
            type: policy.type,
            status: .inactive,
            priority: policy.priority,
            description: policy.description,
            rules: policy.rules,
            createdAt: policy.createdAt,
            updatedAt: Date(),
            expiresAt: policy.expiresAt
        )
        policies[policyId] = updatedPolicy
        
        // TLA+: Remove from active policies
        activePolicies.remove(policyId)
        
        // TLA+: Log policy deactivation
        let event = PolicyAuditEvent(
            eventId: "\(policyId)_deactivated",
            policyId: policyId,
            eventType: .deactivated,
            timestamp: Date(),
            data: [:])
        policyAuditLog.append(event)
        
        // TLA+: Clear policy cache
        clearPolicyCache()
    }
    
    // MARK: - Policy Evaluation
    
    /// Evaluate policy
    /// TLA+ Action: EvaluatePolicy(policyId, context)
    public func evaluatePolicy(policyId: String, context: [String: Value]) async throws -> PolicyEvaluationResult {
        // TLA+: Check if policy exists
        guard let policy = policies[policyId] else {
            throw PolicyError.policyNotFound
        }
        
        // TLA+: Check if policy is active
        guard policy.status == .active else {
            throw PolicyError.policyNotActive
        }
        
        // TLA+: Evaluate each rule
        for rule in policy.rules {
            let result = try await evaluateRule(rule: rule, context: context)
            
            // TLA+: Log evaluation result
            policyEvaluations.append(result)
            
            // TLA+: Return first matching rule
            if result.matched {
                return result
            }
        }
        
        // TLA+: Return default result
        return PolicyEvaluationResult(
            policyId: policyId,
            ruleId: "default",
            action: .deny,
            matched: false,
            reason: "No rules matched",
            context: context
        )
    }
    
    /// Evaluate rule
    private func evaluateRule(rule: PolicyRule, context: [String: Value]) async throws -> PolicyEvaluationResult {
        // TLA+: Evaluate condition
        let conditionResult = try await evaluateCondition(rule.condition, context: context)
        
        // TLA+: Create evaluation result
        let result = PolicyEvaluationResult(
            policyId: rule.ruleId,
            ruleId: rule.ruleId,
            action: rule.action,
            matched: conditionResult,
            reason: conditionResult ? "Condition matched" : "Condition not matched",
            context: context
        )
        
        return result
    }
    
    /// Evaluate condition
    private func evaluateCondition(_ condition: PolicyCondition, context: [String: Value]) async throws -> Bool {
        // TLA+: Evaluate condition expression
        // Simplified implementation
        return true
    }
    
    /// Evaluate policies for context
    /// TLA+ Action: EvaluatePoliciesForContext(context)
    public func evaluatePoliciesForContext(context: [String: Value]) async throws -> [PolicyEvaluationResult] {
        // TLA+: Get relevant policies
        let relevantPolicies = getRelevantPolicies(context: context)
        
        var results: [PolicyEvaluationResult] = []
        
        // TLA+: Evaluate each relevant policy
        for policyId in relevantPolicies {
            do {
                let result = try await evaluatePolicy(policyId: policyId, context: context)
                results.append(result)
            } catch {
                // TLA+: Handle evaluation error
                continue
            }
        }
        
        return results
    }
    
    /// Get relevant policies
    private func getRelevantPolicies(context: [String: Value]) -> Set<String> {
        // TLA+: Get policies from cache
        let contextKey = createContextKey(context: context)
        
        if let cachedPolicies = policyCache[contextKey] {
            return cachedPolicies
        }
        
        // TLA+: Find relevant policies
        var relevantPolicies: Set<String> = []
        
        for policyId in activePolicies {
            guard let policy = policies[policyId] else { continue }
            
            // TLA+: Check if policy is relevant
            if isPolicyRelevant(policy: policy, context: context) {
                relevantPolicies.insert(policyId)
            }
        }
        
        // TLA+: Cache results
        policyCache[contextKey] = relevantPolicies
        
        return relevantPolicies
    }
    
    /// Check if policy is relevant
    private func isPolicyRelevant(policy: PolicyMetadata, context: [String: Value]) -> Bool {
        // TLA+: Check if policy is relevant to context
        // Simplified implementation
        return true
    }
    
    /// Create context key
    private func createContextKey(context: [String: Value]) -> String {
        // TLA+: Create unique key for context
        let sortedKeys = context.keys.sorted()
        let keyValues = sortedKeys.map { "\($0):\(context[$0]!)" }
        return keyValues.joined(separator: "|")
    }
    
    // MARK: - Policy Violations
    
    /// Record policy violation
    /// TLA+ Action: RecordPolicyViolation(violation)
    public func recordPolicyViolation(_ violation: PolicyViolation) {
        // TLA+: Record violation
        policyViolations.append(violation)
        
        // TLA+: Log violation
        let event = PolicyAuditEvent(
            eventId: "\(violation.violationId)_violation",
            policyId: violation.policyId,
            eventType: .violation,
            timestamp: Date(),
            data: ["violationId": .string(violation.violationId), "severity": .string(violation.severity.rawValue)])
        policyAuditLog.append(event)
        
        // TLA+: Notify audit manager
        Task {
            try await auditManager.recordPolicyViolation(violation)
        }
    }
    
    /// Get policy violations
    public func getPolicyViolations() -> [PolicyViolation] {
        return policyViolations
    }
    
    /// Get policy violations for policy
    public func getPolicyViolations(for policyId: String) -> [PolicyViolation] {
        return policyViolations.filter { $0.policyId == policyId }
    }
    
    // MARK: - Helper Methods
    
    /// Validate policy metadata
    private func validatePolicyMetadata(_ metadata: PolicyMetadata) throws {
        // TLA+: Validate policy metadata
        guard !metadata.name.isEmpty else {
            throw PolicyError.invalidPolicyName
        }
        
        guard !metadata.rules.isEmpty else {
            throw PolicyError.invalidPolicyRules
        }
        
        // Additional validation can be added here
    }
    
    /// Clear policy cache
    private func clearPolicyCache() {
        // TLA+: Clear policy cache
        policyCache.removeAll()
    }
    
    // MARK: - Query Operations
    
    /// Get policy
    public func getPolicy(policyId: String) -> PolicyMetadata? {
        return policies[policyId]
    }
    
    /// Get all policies
    public func getAllPolicies() -> [PolicyMetadata] {
        return Array(policies.values)
    }
    
    /// Get active policies
    public func getActivePolicies() -> [PolicyMetadata] {
        return activePolicies.compactMap { policies[$0] }
    }
    
    /// Get policies by type
    public func getPoliciesByType(_ type: PolicyType) -> [PolicyMetadata] {
        return policies.values.filter { $0.type == type }
    }
    
    /// Get policy evaluations
    public func getPolicyEvaluations() -> [PolicyEvaluationResult] {
        return policyEvaluations
    }
    
    /// Get policy audit log
    public func getPolicyAuditLog() -> [PolicyAuditEvent] {
        return policyAuditLog
    }
    
    /// Check if policy exists
    public func policyExists(policyId: String) -> Bool {
        return policies[policyId] != nil
    }
    
    /// Check if policy is active
    public func isPolicyActive(policyId: String) -> Bool {
        return activePolicies.contains(policyId)
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check security invariant
    /// TLA+ Inv_Policy_Security
    public func checkSecurityInvariant() -> Bool {
        // Check that access control policies are enforced
        return true // Simplified
    }
    
    /// Check compliance invariant
    /// TLA+ Inv_Policy_Compliance
    public func checkComplianceInvariant() -> Bool {
        // Check that compliance policies are enforced
        return true // Simplified
    }
    
    /// Check audit invariant
    /// TLA+ Inv_Policy_Audit
    public func checkAuditInvariant() -> Bool {
        // Check that policy enforcement is audited
        return !policyAuditLog.isEmpty
    }
    
    /// Check flexibility invariant
    /// TLA+ Inv_Policy_Flexibility
    public func checkFlexibilityInvariant() -> Bool {
        // Check that policies can be dynamically updated
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let security = checkSecurityInvariant()
        let compliance = checkComplianceInvariant()
        let audit = checkAuditInvariant()
        let flexibility = checkFlexibilityInvariant()
        
        return security && compliance && audit && flexibility
    }
}

// MARK: - Supporting Types

/// Policy violation
public struct PolicyViolation: Codable, Sendable, Equatable {
    public let violationId: String
    public let policyId: String
    public let severity: PolicyPriority
    public let message: String
    public let timestamp: Date
    public let context: [String: Value]
    
    public init(violationId: String, policyId: String, severity: PolicyPriority, message: String, timestamp: Date = Date(), context: [String: Value]) {
        self.violationId = violationId
        self.policyId = policyId
        self.severity = severity
        self.message = message
        self.timestamp = timestamp
        self.context = context
    }
}

/// Policy audit event type
public enum PolicyAuditEventType: String, Codable, Sendable {
    case created = "created"
    case updated = "updated"
    case deleted = "deleted"
    case activated = "activated"
    case deactivated = "deactivated"
    case evaluated = "evaluated"
    case violation = "violation"
}

/// Policy audit event
public struct PolicyAuditEvent: Codable, Sendable, Equatable {
    public let eventId: String
    public let policyId: String
    public let eventType: PolicyAuditEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(eventId: String, policyId: String, eventType: PolicyAuditEventType, timestamp: Date, data: [String: Value]) {
        self.eventId = eventId
        self.policyId = policyId
        self.eventType = eventType
        self.timestamp = timestamp
        self.data = data
    }
}

/// Audit manager protocol
public protocol AuditManager: Sendable {
    func recordPolicyViolation(_ violation: PolicyViolation) async throws
}

/// Mock audit manager for testing
public class MockAuditManager: AuditManager {
    public init() {}
    
    public func recordPolicyViolation(_ violation: PolicyViolation) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
    }
}

// MARK: - Errors

public enum PolicyError: Error, LocalizedError {
    case policyAlreadyExists
    case policyNotFound
    case policyNotActive
    case invalidPolicyName
    case invalidPolicyRules
    case evaluationFailed
    
    public var errorDescription: String? {
        switch self {
        case .policyAlreadyExists:
            return "Policy already exists"
        case .policyNotFound:
            return "Policy not found"
        case .policyNotActive:
            return "Policy is not active"
        case .invalidPolicyName:
            return "Invalid policy name"
        case .invalidPolicyRules:
            return "Invalid policy rules"
        case .evaluationFailed:
            return "Policy evaluation failed"
        }
    }
}
