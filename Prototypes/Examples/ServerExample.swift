//
//  ServerExample.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Example usage of ColibrDB HTTP server.

import Foundation
import ColibriCore

/// Example usage of ColibrDB HTTP server
public class ServerExample {
    
    public static func runExample() {
        print("🚀 ColibrDB HTTP Server Example")
        print("=================================")
        
        // Create database configuration
        let config = DBConfig(
            dataDir: "./server_data",
            pageSize: 8192,
            dataBufferPoolPages: 1000,
            indexBufferPoolPages: 500,
            walEnabled: true,
            walFullFSyncEnabled: false,
            walCompression: .none,
            ioSequentialReadHint: true,
            autoCompactionEnabled: true,
            autoCompactionIntervalSeconds: 300,
            autoCompactionPagesPerRun: 32,
            lockTimeoutSeconds: 30.0
        )
        
        // Initialize ColibrDB
        let colibriDB = ColibriDB(config: config)
        
        do {
            // Initialize the system
            try colibriDB.initialize()
            print("✅ Database initialized")
            
            // Start the system
            try colibriDB.start()
            print("✅ Database started")
            
            // Create and start HTTP server
            let server = ColibriServer(colibriDB: colibriDB, host: "localhost", port: 8080)
            try server.start()
            print("✅ HTTP server started on http://localhost:8080")
            
            // Print server information
            print("")
            print("🌐 Server Information:")
            print("  URL: http://localhost:8080")
            print("  Health: http://localhost:8080/health")
            print("  Status: http://localhost:8080/status")
            print("  API: http://localhost:8080/api/v1/")
            print("")
            
            // Demonstrate API usage
            demonstrateAPIUsage()
            
            // Keep server running
            print("🔄 Server is running. Press Ctrl+C to stop")
            print("")
            
            // Set up signal handlers for graceful shutdown
            setupSignalHandlers(server: server, colibriDB: colibriDB)
            
            // Keep the server running
            RunLoop.main.run()
            
        } catch {
            print("❌ Error: \(error.localizedDescription)")
        }
    }
    
    /// Demonstrates API usage
    private static func demonstrateAPIUsage() {
        print("📚 API Usage Examples:")
        print("=====================")
        print("")
        
        // Health check
        print("1. Health Check:")
        print("   curl http://localhost:8080/health")
        print("")
        
        // System status
        print("2. System Status:")
        print("   curl http://localhost:8080/status")
        print("")
        
        // Create table
        print("3. Create Table:")
        print("   curl -X POST http://localhost:8080/api/v1/tables \\")
        print("     -H 'Content-Type: application/json' \\")
        print("     -d '{")
        print("       \"name\": \"users\",")
        print("       \"columns\": [")
        print("         {\"name\": \"id\", \"type\": \"int\", \"nullable\": false},")
        print("         {\"name\": \"name\", \"type\": \"string\", \"nullable\": true},")
        print("         {\"name\": \"email\", \"type\": \"string\", \"nullable\": true}")
        print("       ]")
        print("     }'")
        print("")
        
        // Execute query
        print("4. Execute Query:")
        print("   curl -X POST http://localhost:8080/api/v1/query \\")
        print("     -H 'Content-Type: application/json' \\")
        print("     -d '{\"sql\": \"SELECT * FROM users WHERE id > 1\"}'")
        print("")
        
        // Begin transaction
        print("5. Begin Transaction:")
        print("   curl -X POST http://localhost:8080/api/v1/transactions/begin")
        print("")
        
        // Create index
        print("6. Create Index:")
        print("   curl -X POST http://localhost:8080/api/v1/indexes \\")
        print("     -H 'Content-Type: application/json' \\")
        print("     -d '{")
        print("       \"name\": \"users_id_idx\",")
        print("       \"table\": \"users\",")
        print("       \"columns\": [\"id\"],")
        print("       \"type\": \"BTREE\"")
        print("     }'")
        print("")
        
        // Get metrics
        print("7. Get Metrics:")
        print("   curl http://localhost:8080/api/v1/monitoring/metrics")
        print("")
        
        // Run tests
        print("8. Run Tests:")
        print("   curl -X POST http://localhost:8080/api/v1/testing/run")
        print("")
        
        // Run benchmarks
        print("9. Run Benchmarks:")
        print("   curl -X POST http://localhost:8080/api/v1/performance/benchmarks")
        print("")
        
        print("💡 Tip: Use the test script to test all endpoints:")
        print("   ./Scripts/test-server.sh all")
        print("")
    }
    
    /// Sets up signal handlers for graceful shutdown
    private static func setupSignalHandlers(server: ColibriServer, colibriDB: ColibriDB) {
        // Handle SIGINT (Ctrl+C)
        signal(SIGINT) { _ in
            print("\n🛑 Shutting down server...")
            
            server.stop()
            
            do {
                try colibriDB.stop()
                try colibriDB.shutdown()
                print("✅ Server shutdown completed")
            } catch {
                print("❌ Error during shutdown: \(error.localizedDescription)")
            }
            
            exit(0)
        }
        
        // Handle SIGTERM
        signal(SIGTERM) { _ in
            print("\n🛑 Shutting down server...")
            
            server.stop()
            
            do {
                try colibriDB.stop()
                try colibriDB.shutdown()
                print("✅ Server shutdown completed")
            } catch {
                print("❌ Error during shutdown: \(error.localizedDescription)")
            }
            
            exit(0)
        }
    }
}

/// HTTP client for testing the server
public class HTTPClient {
    private let baseURL: String
    
    public init(baseURL: String = "http://localhost:8080") {
        self.baseURL = baseURL
    }
    
    /// Makes an HTTP request
    public func request(method: String, endpoint: String, data: Data? = nil) -> (Data?, Int) {
        let url = URL(string: "\(baseURL)\(endpoint)")!
        var request = URLRequest(url: url)
        request.httpMethod = method
        
        if let data = data {
            request.httpBody = data
            request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        }
        
        let semaphore = DispatchSemaphore(value: 0)
        var responseData: Data?
        var statusCode: Int = 0
        
        URLSession.shared.dataTask(with: request) { data, response, error in
            responseData = data
            if let httpResponse = response as? HTTPURLResponse {
                statusCode = httpResponse.statusCode
            }
            semaphore.signal()
        }.resume()
        
        semaphore.wait()
        return (responseData, statusCode)
    }
    
    /// Health check
    public func healthCheck() -> (Data?, Int) {
        return request(method: "GET", endpoint: "/health")
    }
    
    /// Get system status
    public func getStatus() -> (Data?, Int) {
        return request(method: "GET", endpoint: "/status")
    }
    
    /// Get system info
    public func getInfo() -> (Data?, Int) {
        return request(method: "GET", endpoint: "/info")
    }
    
    /// Create table
    public func createTable(name: String, columns: [[String: Any]]) -> (Data?, Int) {
        let data = try! JSONSerialization.data(withJSONObject: [
            "name": name,
            "columns": columns
        ])
        return request(method: "POST", endpoint: "/api/v1/tables", data: data)
    }
    
    /// Execute query
    public func executeQuery(sql: String) -> (Data?, Int) {
        let data = try! JSONSerialization.data(withJSONObject: [
            "sql": sql
        ])
        return request(method: "POST", endpoint: "/api/v1/query", data: data)
    }
    
    /// Begin transaction
    public func beginTransaction() -> (Data?, Int) {
        return request(method: "POST", endpoint: "/api/v1/transactions/begin")
    }
    
    /// Create index
    public func createIndex(name: String, table: String, columns: [String], type: String) -> (Data?, Int) {
        let data = try! JSONSerialization.data(withJSONObject: [
            "name": name,
            "table": table,
            "columns": columns,
            "type": type
        ])
        return request(method: "POST", endpoint: "/api/v1/indexes", data: data)
    }
    
    /// Get metrics
    public func getMetrics() -> (Data?, Int) {
        return request(method: "GET", endpoint: "/api/v1/monitoring/metrics")
    }
    
    /// Run tests
    public func runTests() -> (Data?, Int) {
        return request(method: "POST", endpoint: "/api/v1/testing/run")
    }
}

/// Example of using the HTTP client
public func demonstrateHTTPClient() {
    print("🔗 HTTP Client Example")
    print("=====================")
    
    let client = HTTPClient()
    
    // Health check
    let (healthData, healthStatus) = client.healthCheck()
    print("Health check: \(healthStatus)")
    if let data = healthData, let json = try? JSONSerialization.jsonObject(with: data) {
        print("Response: \(json)")
    }
    
    // Get status
    let (statusData, statusCode) = client.getStatus()
    print("Status: \(statusCode)")
    if let data = statusData, let json = try? JSONSerialization.jsonObject(with: data) {
        print("Response: \(json)")
    }
    
    // Create table
    let (tableData, tableStatus) = client.createTable(name: "users", columns: [
        ["name": "id", "type": "int", "nullable": false],
        ["name": "name", "type": "string", "nullable": true]
    ])
    print("Create table: \(tableStatus)")
    if let data = tableData, let json = try? JSONSerialization.jsonObject(with: data) {
        print("Response: \(json)")
    }
    
    // Execute query
    let (queryData, queryStatus) = client.executeQuery(sql: "SELECT * FROM users")
    print("Execute query: \(queryStatus)")
    if let data = queryData, let json = try? JSONSerialization.jsonObject(with: data) {
        print("Response: \(json)")
    }
    
    // Get metrics
    let (metricsData, metricsStatus) = client.getMetrics()
    print("Get metrics: \(metricsStatus)")
    if let data = metricsData, let json = try? JSONSerialization.jsonObject(with: data) {
        print("Response: \(json)")
    }
}

/// Main function to run the example
public func main() {
    ServerExample.runExample()
}
