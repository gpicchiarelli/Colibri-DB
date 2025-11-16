import XCTest
@testable import ColibriCore

final class UserCRUDTests: XCTestCase {
    func testUserCRUDFlow() async throws {
        let auth = AuthenticationManager()
        
        // Create
        try await auth.createUser(username: "u1", email: "u1@example.com", password: "Passw0rd!", role: .user)
        XCTAssertNotNil(auth.getUser(username: "u1"))
        
        // Login
        let sessionId = try await auth.authenticate(username: "u1", password: "Passw0rd!")
        XCTAssertFalse(sessionId.isEmpty)
        XCTAssertEqual(auth.getActiveSessionsCount(), 1)
        
        // Update role
        try await auth.updateUserRole(username: "u1", newRole: .admin)
        XCTAssertEqual(auth.getUser(username: "u1")?.role, .admin)
        
        // Change password
        try await auth.changePassword(username: "u1", oldPassword: "Passw0rd!", newPassword: "N3wPassw0rd!")
        // Old password fails
        await XCTAssertAsyncThrowsError(try await auth.authenticate(username: "u1", password: "Passw0rd!"))
        // New password works
        let sessionId2 = try await auth.authenticate(username: "u1", password: "N3wPassw0rd!")
        XCTAssertFalse(sessionId2.isEmpty)
        
        // Delete
        try await auth.deleteUser(username: "u1")
        XCTAssertNil(auth.getUser(username: "u1"))
    }
}

extension XCTestCase {
    func XCTAssertAsyncThrowsError<T>(_ expression: @autoclosure () async throws -> T,
                                      _ message: @autoclosure () -> String = "",
                                      file: StaticString = #filePath, line: UInt = #line) async {
        do {
            _ = try await expression()
            XCTFail(message(), file: file, line: line)
        } catch {
            // success
        }
    }
}


