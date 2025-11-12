import Foundation
import Testing
@testable import ColibriCore

@Suite("Authentication Tests")
struct AuthenticationTests {
    
    @Test("Password hashing uses PBKDF2 parameters")
    func testPasswordHashingPBKDF2() throws {
        let manager = AuthenticationManager()
        let username = "pbkdf2_user"
        let password = "SecurePass1"
        let email = "pbkdf2_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        let metadata = try #require(manager.getUser(username: username))
        
        #expect(metadata.passwordHash != password)
        #expect(metadata.passwordHash.count > 0)
        #expect(metadata.salt.count > 0)
        
        let saltData = try #require(Data(base64Encoded: metadata.salt))
        let hashData = try #require(Data(base64Encoded: metadata.passwordHash))
        
        #expect(saltData.count == 16)
        #expect(hashData.count == 32)
    }
    
    @Test("Successful authentication returns active session")
    func testSuccessfulAuthentication() async throws {
        let manager = AuthenticationManager()
        let username = "auth_success_user"
        let password = "ValidPass1"
        let email = "auth_success_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        let session = try await manager.authenticateUser(username: username, password: password)
        
        #expect(session.username == username)
        #expect(session.isActive)
    }
    
    @Test("Authentication fails with wrong password")
    func testAuthenticationFailsWithWrongPassword() async throws {
        let manager = AuthenticationManager()
        let username = "auth_failure_user"
        let password = "ValidPass1"
        let email = "auth_failure_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        await #expect(throws: AuthenticationError.invalidCredentials) {
            try await manager.authenticateUser(username: username, password: "WrongPass1")
        }
    }
}

