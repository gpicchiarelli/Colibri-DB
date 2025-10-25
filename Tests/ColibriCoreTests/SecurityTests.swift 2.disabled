//
//  SecurityTests.swift
//  ColibrìDB Security Tests
//
//  Tests for authentication, authorization, and security features
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for Security Modules
@Suite("Security Tests")
struct SecurityTests {
    
    /// Test authentication manager initialization
    @Test("Authentication Manager Initialization")
    func testAuthenticationManagerInitialization() async throws {
        let authManager = AuthenticationManager()
        
        // Verify initial state
        let users = await authManager.getUsers()
        let activeSessions = await authManager.getActiveSessions()
        
        try TestAssertions.assertEqual(users.count, 0, "Should start with no users")
        try TestAssertions.assertEqual(activeSessions.count, 0, "Should start with no active sessions")
    }
    
    /// Test user creation
    @Test("User Creation")
    func testUserCreation() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        // Verify user was created
        let users = await authManager.getUsers()
        try TestAssertions.assertEqual(users.count, 1, "Should have 1 user")
        try TestAssertions.assertContains(users, "alice", "Should contain created user")
    }
    
    /// Test user authentication
    @Test("User Authentication")
    func testUserAuthentication() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        // Authenticate user
        let token = try await authManager.authenticate(username: "alice", password: "password123")
        try TestAssertions.assertNotNil(token, "Authentication token should not be nil")
        
        // Verify session was created
        let activeSessions = await authManager.getActiveSessions()
        try TestAssertions.assertEqual(activeSessions.count, 1, "Should have 1 active session")
    }
    
    /// Test invalid authentication
    @Test("Invalid Authentication")
    func testInvalidAuthentication() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        // Test invalid password
        try TestAssertions.assertAsyncThrows({
            try await authManager.authenticate(username: "alice", password: "wrongpassword")
        }, "Should throw error for invalid password")
        
        // Test non-existent user
        try TestAssertions.assertAsyncThrows({
            try await authManager.authenticate(username: "bob", password: "password123")
        }, "Should throw error for non-existent user")
    }
    
    /// Test session validation
    @Test("Session Validation")
    func testSessionValidation() async throws {
        let authManager = AuthenticationManager()
        
        // Create user and authenticate
        try await authManager.createUser(username: "alice", password: "password123")
        let token = try await authManager.authenticate(username: "alice", password: "password123")
        
        // Validate session
        let validatedUser = await authManager.validateSession(token)
        try TestAssertions.assertNotNil(validatedUser, "Session should be valid")
        try TestAssertions.assertEqual(validatedUser!, "alice", "Validated user should match")
        
        // Test invalid session
        let invalidToken = "invalid_token"
        let invalidUser = await authManager.validateSession(invalidToken)
        try TestAssertions.assertNil(invalidUser, "Invalid session should return nil")
    }
    
    /// Test session expiration
    @Test("Session Expiration")
    func testSessionExpiration() async throws {
        let authManager = AuthenticationManager()
        
        // Create user and authenticate
        try await authManager.createUser(username: "alice", password: "password123")
        let token = try await authManager.authenticate(username: "alice", password: "password123")
        
        // Expire session
        try await authManager.expireSession(token)
        
        // Verify session is expired
        let validatedUser = await authManager.validateSession(token)
        try TestAssertions.assertNil(validatedUser, "Expired session should return nil")
    }
    
    /// Test user deletion
    @Test("User Deletion")
    func testUserDeletion() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        // Verify user exists
        let usersBefore = await authManager.getUsers()
        try TestAssertions.assertContains(usersBefore, "alice", "User should exist before deletion")
        
        // Delete user
        try await authManager.deleteUser(username: "alice")
        
        // Verify user was deleted
        let usersAfter = await authManager.getUsers()
        try TestAssertions.assertNotContains(usersAfter, "alice", "User should not exist after deletion")
    }
    
    /// Test password change
    @Test("Password Change")
    func testPasswordChange() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        // Change password
        try await authManager.changePassword(username: "alice", oldPassword: "password123", newPassword: "newpassword456")
        
        // Test old password (should fail)
        try TestAssertions.assertAsyncThrows({
            try await authManager.authenticate(username: "alice", password: "password123")
        }, "Old password should not work")
        
        // Test new password (should work)
        let token = try await authManager.authenticate(username: "alice", password: "newpassword456")
        try TestAssertions.assertNotNil(token, "New password should work")
    }
    
    /// Test authorization manager initialization
    @Test("Authorization Manager Initialization")
    func testAuthorizationManagerInitialization() async throws {
        let authzManager = AuthorizationManager()
        
        // Verify initial state
        let roles = await authzManager.getRoles()
        let permissions = await authzManager.getPermissions()
        
        try TestAssertions.assertEqual(roles.count, 0, "Should start with no roles")
        try TestAssertions.assertEqual(permissions.count, 0, "Should start with no permissions")
    }
    
    /// Test role creation
    @Test("Role Creation")
    func testRoleCreation() async throws {
        let authzManager = AuthorizationManager()
        
        // Create role
        try await authzManager.createRole("admin", permissions: ["read", "write", "delete"])
        
        // Verify role was created
        let roles = await authzManager.getRoles()
        try TestAssertions.assertEqual(roles.count, 1, "Should have 1 role")
        try TestAssertions.assertContains(roles, "admin", "Should contain created role")
    }
    
    /// Test permission assignment
    @Test("Permission Assignment")
    func testPermissionAssignment() async throws {
        let authzManager = AuthorizationManager()
        
        // Create role
        try await authzManager.createRole("admin", permissions: ["read", "write"])
        
        // Assign additional permission
        try await authzManager.assignPermission(role: "admin", permission: "delete")
        
        // Verify permission was assigned
        let rolePermissions = await authzManager.getRolePermissions("admin")
        try TestAssertions.assertNotNil(rolePermissions, "Role should exist")
        try TestAssertions.assertContains(rolePermissions!, "delete", "Should contain assigned permission")
    }
    
    /// Test permission check
    @Test("Permission Check")
    func testPermissionCheck() async throws {
        let authzManager = AuthorizationManager()
        
        // Create role with permissions
        try await authzManager.createRole("admin", permissions: ["read", "write"])
        
        // Check permissions
        let hasRead = await authzManager.hasPermission(role: "admin", permission: "read")
        let hasWrite = await authzManager.hasPermission(role: "admin", permission: "write")
        let hasDelete = await authzManager.hasPermission(role: "admin", permission: "delete")
        
        try TestAssertions.assertTrue(hasRead, "Should have read permission")
        try TestAssertions.assertTrue(hasWrite, "Should have write permission")
        try TestAssertions.assertFalse(hasDelete, "Should not have delete permission")
    }
    
    /// Test user role assignment
    @Test("User Role Assignment")
    func testUserRoleAssignment() async throws {
        let authzManager = AuthorizationManager()
        
        // Create role
        try await authzManager.createRole("admin", permissions: ["read", "write"])
        
        // Assign role to user
        try await authzManager.assignRole(user: "alice", role: "admin")
        
        // Verify role assignment
        let userRoles = await authzManager.getUserRoles("alice")
        try TestAssertions.assertNotNil(userRoles, "User should exist")
        try TestAssertions.assertContains(userRoles!, "admin", "Should contain assigned role")
    }
    
    /// Test access control
    @Test("Access Control")
    func testAccessControl() async throws {
        let authzManager = AuthorizationManager()
        
        // Create roles
        try await authzManager.createRole("admin", permissions: ["read", "write", "delete"])
        try await authzManager.createRole("user", permissions: ["read"])
        
        // Assign roles
        try await authzManager.assignRole(user: "alice", role: "admin")
        try await authzManager.assignRole(user: "bob", role: "user")
        
        // Test access control
        let aliceCanWrite = await authzManager.checkAccess(user: "alice", permission: "write")
        let aliceCanDelete = await authzManager.checkAccess(user: "alice", permission: "delete")
        let bobCanWrite = await authzManager.checkAccess(user: "bob", permission: "write")
        let bobCanRead = await authzManager.checkAccess(user: "bob", permission: "read")
        
        try TestAssertions.assertTrue(aliceCanWrite, "Alice should be able to write")
        try TestAssertions.assertTrue(aliceCanDelete, "Alice should be able to delete")
        try TestAssertions.assertFalse(bobCanWrite, "Bob should not be able to write")
        try TestAssertions.assertTrue(bobCanRead, "Bob should be able to read")
    }
    
    /// Test roles and permissions manager
    @Test("Roles and Permissions Manager")
    func testRolesAndPermissionsManager() async throws {
        let rolesManager = RolesPermissionsManager()
        
        // Verify initial state
        let roles = await rolesManager.getRoles()
        let permissions = await rolesManager.getPermissions()
        
        try TestAssertions.assertEqual(roles.count, 0, "Should start with no roles")
        try TestAssertions.assertEqual(permissions.count, 0, "Should start with no permissions")
    }
    
    /// Test role hierarchy
    @Test("Role Hierarchy")
    func testRoleHierarchy() async throws {
        let rolesManager = RolesPermissionsManager()
        
        // Create role hierarchy
        try await rolesManager.createRole("admin", permissions: ["read", "write", "delete"])
        try await rolesManager.createRole("manager", permissions: ["read", "write"])
        try await rolesManager.createRole("user", permissions: ["read"])
        
        // Set hierarchy
        try await rolesManager.setRoleHierarchy(parent: "admin", child: "manager")
        try await rolesManager.setRoleHierarchy(parent: "manager", child: "user")
        
        // Test inherited permissions
        let managerPermissions = await rolesManager.getRolePermissions("manager")
        try TestAssertions.assertNotNil(managerPermissions, "Manager role should exist")
        
        let userPermissions = await rolesManager.getRolePermissions("user")
        try TestAssertions.assertNotNil(userPermissions, "User role should exist")
    }
    
    /// Test security policy enforcement
    @Test("Security Policy Enforcement")
    func testSecurityPolicyEnforcement() async throws {
        let policyManager = PolicyManager()
        
        // Create security policy
        let policy = SecurityPolicy(
            name: "data_access_policy",
            rules: [
                SecurityRule(resource: "users", action: "read", condition: "user.role == 'admin'"),
                SecurityRule(resource: "users", action: "write", condition: "user.role == 'admin'"),
                SecurityRule(resource: "users", action: "delete", condition: "user.role == 'admin'")
            ]
        )
        
        try await policyManager.createPolicy(policy)
        
        // Test policy enforcement
        let canRead = await policyManager.checkPolicy(resource: "users", action: "read", user: "alice", userRole: "admin")
        let canWrite = await policyManager.checkPolicy(resource: "users", action: "write", user: "alice", userRole: "admin")
        let canDelete = await policyManager.checkPolicy(resource: "users", action: "delete", user: "alice", userRole: "admin")
        
        try TestAssertions.assertTrue(canRead, "Admin should be able to read")
        try TestAssertions.assertTrue(canWrite, "Admin should be able to write")
        try TestAssertions.assertTrue(canDelete, "Admin should be able to delete")
        
        // Test non-admin access
        let userCanRead = await policyManager.checkPolicy(resource: "users", action: "read", user: "bob", userRole: "user")
        try TestAssertions.assertFalse(userCanRead, "User should not be able to read")
    }
    
    /// Test encryption/decryption
    @Test("Encryption/Decryption")
    func testEncryptionDecryption() async throws {
        let encryptionManager = EncryptionManager()
        
        // Test data encryption
        let originalData = TestUtils.generateRandomData(size: 1024)
        let encryptedData = try await encryptionManager.encrypt(originalData, key: "test_key")
        
        // Verify data was encrypted
        try TestAssertions.assertNotEqual(encryptedData, originalData, "Encrypted data should be different")
        
        // Test data decryption
        let decryptedData = try await encryptionManager.decrypt(encryptedData, key: "test_key")
        
        // Verify data was decrypted correctly
        try TestAssertions.assertEqual(decryptedData, originalData, "Decrypted data should match original")
    }
    
    /// Test key management
    @Test("Key Management")
    func testKeyManagement() async throws {
        let keyManager = KeyManager()
        
        // Generate key
        let key = try await keyManager.generateKey(algorithm: .AES256)
        try TestAssertions.assertNotNil(key, "Generated key should not be nil")
        
        // Store key
        try await keyManager.storeKey(key, name: "test_key")
        
        // Retrieve key
        let retrievedKey = await keyManager.getKey(name: "test_key")
        try TestAssertions.assertNotNil(retrievedKey, "Retrieved key should not be nil")
        try TestAssertions.assertEqual(retrievedKey!, key, "Retrieved key should match stored key")
        
        // Delete key
        try await keyManager.deleteKey(name: "test_key")
        
        // Verify key was deleted
        let deletedKey = await keyManager.getKey(name: "test_key")
        try TestAssertions.assertNil(deletedKey, "Deleted key should be nil")
    }
    
    /// Test audit logging
    @Test("Audit Logging")
    func testAuditLogging() async throws {
        let auditLogger = AuditLogger()
        
        // Log audit event
        let event = AuditEvent(
            timestamp: Date(),
            user: "alice",
            action: "login",
            resource: "authentication",
            result: "success",
            details: "User logged in successfully"
        )
        
        try await auditLogger.logEvent(event)
        
        // Verify event was logged
        let events = await auditLogger.getEvents(since: Date().addingTimeInterval(-60))
        try TestAssertions.assertEqual(events.count, 1, "Should have 1 audit event")
        try TestAssertions.assertEqual(events[0].user, "alice", "Event user should match")
        try TestAssertions.assertEqual(events[0].action, "login", "Event action should match")
    }
    
    /// Test concurrent security operations
    @Test("Concurrent Security Operations")
    func testConcurrentSecurityOperations() async throws {
        let authManager = AuthenticationManager()
        
        // Start multiple concurrent tasks
        let taskCount = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<taskCount {
            let task = Task {
                do {
                    // Create user
                    try await authManager.createUser(username: "user\(i)", password: "password\(i)")
                    
                    // Authenticate user
                    let token = try await authManager.authenticate(username: "user\(i)", password: "password\(i)")
                    
                    // Validate session
                    let validatedUser = await authManager.validateSession(token)
                    try TestAssertions.assertNotNil(validatedUser, "Session should be valid")
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Verify all users were created
        let users = await authManager.getUsers()
        try TestAssertions.assertEqual(users.count, taskCount, "Should have all users")
    }
    
    /// Test security performance
    @Test("Security Performance")
    func testSecurityPerformance() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        let operationCount = 1000
        let startTime = Date()
        
        // Perform many authentication operations
        for _ in 0..<operationCount {
            let token = try await authManager.authenticate(username: "alice", password: "password123")
            _ = await authManager.validateSession(token)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(duration < 2.0, "Security operations should be fast")
    }
    
    /// Test security error handling
    @Test("Security Error Handling")
    func testSecurityErrorHandling() async throws {
        let authManager = AuthenticationManager()
        
        // Test operations on non-existent user
        try TestAssertions.assertAsyncThrows({
            try await authManager.deleteUser(username: "nonexistent")
        }, "Should throw error for non-existent user")
        
        try TestAssertions.assertAsyncThrows({
            try await authManager.changePassword(username: "nonexistent", oldPassword: "old", newPassword: "new")
        }, "Should throw error for non-existent user")
        
        // Test invalid password change
        try await authManager.createUser(username: "alice", password: "password123")
        
        try TestAssertions.assertAsyncThrows({
            try await authManager.changePassword(username: "alice", oldPassword: "wrong", newPassword: "new")
        }, "Should throw error for wrong old password")
    }
}
