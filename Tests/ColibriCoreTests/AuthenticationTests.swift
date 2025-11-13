import Foundation
import XCTest
@testable import ColibriCore

final class AuthenticationTests {
    
    func testPasswordHashingPBKDF2() throws {
        let manager = AuthenticationManager()
        let username = "pbkdf2_user"
        let password = "SecurePass1"
        let email = "pbkdf2_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        let metadata = try XCTUnwrap(manager.getUser(username: username))
        
        XCTAssert(metadata.passwordHash != password)
        XCTAssert(metadata.passwordHash.count > 0)
        XCTAssert(metadata.salt.count > 0)
        
        let saltData = try XCTUnwrap(Data(base64Encoded: metadata.salt))
        let hashData = try XCTUnwrap(Data(base64Encoded: metadata.passwordHash))
        
        XCTAssert(saltData.count == 16)
        XCTAssert(hashData.count == 32)
    }
    
    func testSuccessfulAuthentication() async throws {
        let manager = AuthenticationManager()
        let username = "auth_success_user"
        let password = "ValidPass1"
        let email = "auth_success_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        let session = try await manager.authenticateUser(username: username, password: password)
        
        XCTAssert(session.username == username)
        XCTAssert(session.isActive)
    }
    
    func testAuthenticationFailsWithWrongPassword() async throws {
        let manager = AuthenticationManager()
        let username = "auth_failure_user"
        let password = "ValidPass1"
        let email = "auth_failure_user@example.com"
        
        try manager.createUser(username: username, email: email, password: password, role: .user)
        
        do {
            try await manager.authenticateUser(username: username, password: "WrongPass1")
            XCTFail("Should have thrown AuthenticationError.invalidCredentials")
        } catch {
            // Expected
        }
    }
}


