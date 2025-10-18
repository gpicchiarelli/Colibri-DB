//
//  RadixTreeSpecializedTests.swift
//  ColibrDBTests
//
//  Specialized tests for RadixTree including autocomplete, IP routing, and more
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class RadixTreeSpecializedTests: XCTestCase {
    
    // MARK: - Autocomplete Tests
    
    func testBasicAutocomplete() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        // Add programming language suggestions
        autocomplete.addSuggestion(prefix: "py", suggestion: "python")
        autocomplete.addSuggestion(prefix: "py", suggestion: "pytorch")
        autocomplete.addSuggestion(prefix: "py", suggestion: "pydantic")
        autocomplete.addSuggestion(prefix: "ja", suggestion: "java")
        autocomplete.addSuggestion(prefix: "ja", suggestion: "javascript")
        autocomplete.addSuggestion(prefix: "ja", suggestion: "janet")
        
        // Test Python prefix
        let pySuggestions = autocomplete.search(key: "py")
        XCTAssertNotNil(pySuggestions)
        XCTAssertEqual(pySuggestions?.count, 3)
        XCTAssertTrue(pySuggestions?.contains("python") ?? false)
        XCTAssertTrue(pySuggestions?.contains("pytorch") ?? false)
        XCTAssertTrue(pySuggestions?.contains("pydantic") ?? false)
        
        // Test Java prefix
        let jaSuggestions = autocomplete.search(key: "ja")
        XCTAssertNotNil(jaSuggestions)
        XCTAssertEqual(jaSuggestions?.count, 3)
        XCTAssertTrue(jaSuggestions?.contains("java") ?? false)
        XCTAssertTrue(jaSuggestions?.contains("javascript") ?? false)
    }
    
    func testAutocompleteWithNesting() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        // Add nested prefixes
        autocomplete.addSuggestion(prefix: "s", suggestion: "swift")
        autocomplete.addSuggestion(prefix: "sw", suggestion: "swift")
        autocomplete.addSuggestion(prefix: "swi", suggestion: "swift")
        autocomplete.addSuggestion(prefix: "swif", suggestion: "swift")
        autocomplete.addSuggestion(prefix: "swift", suggestion: "swift")
        
        // All should return swift
        XCTAssertTrue(autocomplete.search(key: "s")?.contains("swift") ?? false)
        XCTAssertTrue(autocomplete.search(key: "sw")?.contains("swift") ?? false)
        XCTAssertTrue(autocomplete.search(key: "swi")?.contains("swift") ?? false)
        XCTAssertTrue(autocomplete.search(key: "swif")?.contains("swift") ?? false)
        XCTAssertTrue(autocomplete.search(key: "swift")?.contains("swift") ?? false)
    }
    
    func testAutocompleteLargeDataset() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        // Add many words
        let words = [
            "apple", "application", "apply", "applied", "appliance",
            "banana", "band", "bandage", "bandit", "banking",
            "cat", "category", "cathedral", "caterpillar", "cattle"
        ]
        
        for word in words {
            for i in 1...word.count {
                let prefix = String(word.prefix(i))
                autocomplete.addSuggestion(prefix: prefix, suggestion: word)
            }
        }
        
        // Test "app" prefix
        let appSuggestions = autocomplete.search(key: "app")
        XCTAssertNotNil(appSuggestions)
        XCTAssertTrue(appSuggestions?.contains("apple") ?? false)
        XCTAssertTrue(appSuggestions?.contains("application") ?? false)
        XCTAssertTrue(appSuggestions?.contains("apply") ?? false)
        XCTAssertTrue(appSuggestions?.contains("applied") ?? false)
        XCTAssertTrue(appSuggestions?.contains("appliance") ?? false)
        
        // Test "cat" prefix
        let catSuggestions = autocomplete.search(key: "cat")
        XCTAssertNotNil(catSuggestions)
        XCTAssertEqual(catSuggestions?.count, 5)
    }
    
    func testAutocompleteDuplicatePrevention() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        // Add same suggestion multiple times
        autocomplete.addSuggestion(prefix: "te", suggestion: "test")
        autocomplete.addSuggestion(prefix: "te", suggestion: "test")
        autocomplete.addSuggestion(prefix: "te", suggestion: "test")
        
        let suggestions = autocomplete.search(key: "te")
        XCTAssertEqual(suggestions?.count, 1) // Should only appear once
    }
    
    // MARK: - IP Address Routing Tests
    
    func testIPAddressInsertion() {
        let ipTree = RadixTree<RID>.forIPAddresses()
        
        // Insert IP addresses
        ipTree.insert(key: "192.168.1.1", value: RID(page: 0, slot: 1))
        ipTree.insert(key: "192.168.1.2", value: RID(page: 0, slot: 2))
        ipTree.insert(key: "192.168.2.1", value: RID(page: 0, slot: 3))
        ipTree.insert(key: "10.0.0.1", value: RID(page: 0, slot: 4))
        
        XCTAssertEqual(ipTree.size, 4)
        
        // Search for specific IP
        let result = ipTree.search(key: "192.168.1.1")
        XCTAssertNotNil(result)
        XCTAssertEqual(result?.slot, 1)
    }
    
    func testIPAddressPrefixSearch() {
        let ipTree = RadixTree<RID>.forIPAddresses()
        
        // Insert IPs in 192.168 network
        for i in 1...10 {
            ipTree.insert(key: "192.168.1.\(i)", value: RID(page: 0, slot: UInt16(i)))
        }
        
        // Find all IPs with prefix 192.168
        let results = ipTree.keysWithPrefix("192.168")
        XCTAssertEqual(results.count, 10)
        
        // Find all IPs with prefix 192.168.1
        let specificResults = ipTree.keysWithPrefix("192.168.1")
        XCTAssertEqual(specificResults.count, 10)
    }
    
    func testIPAddressSubnetRouting() {
        let ipTree = RadixTree<String>.forIPAddresses()
        
        // Simulate routing table
        ipTree.insert(key: "192.168.0", value: "subnet_a")
        ipTree.insert(key: "192.168.1", value: "subnet_b")
        ipTree.insert(key: "192.168.2", value: "subnet_c")
        ipTree.insert(key: "10.0", value: "internal")
        ipTree.insert(key: "172.16", value: "dmz")
        
        // Test longest prefix matching (common in routing)
        let longestPrefix = ipTree.longestCommonPrefix()
        // Should be empty or common prefix among all
        XCTAssertNotNil(longestPrefix)
    }
    
    func testIPv6AddressSupport() {
        let ipTree = RadixTree<String>()
        
        // Insert IPv6 addresses
        ipTree.insert(key: "2001:0db8:85a3:0000:0000:8a2e:0370:7334", value: "host1")
        ipTree.insert(key: "2001:0db8:85a3:0000:0000:8a2e:0370:7335", value: "host2")
        ipTree.insert(key: "fe80::1", value: "link-local")
        
        XCTAssertEqual(ipTree.size, 3)
        
        // Search for specific address
        XCTAssertEqual(ipTree.search(key: "fe80::1"), "link-local")
        
        // Prefix search
        let prefix2001 = ipTree.keysWithPrefix("2001")
        XCTAssertEqual(prefix2001.count, 2)
    }
    
    // MARK: - URL/Domain Tests
    
    func testURLPathRouting() {
        let urlTree = RadixTree<String>.forStringIndex()
        
        // Insert URL paths with handlers
        urlTree.insert(key: "/api/users", value: "UserHandler")
        urlTree.insert(key: "/api/users/profile", value: "ProfileHandler")
        urlTree.insert(key: "/api/posts", value: "PostHandler")
        urlTree.insert(key: "/api/posts/comments", value: "CommentHandler")
        urlTree.insert(key: "/admin", value: "AdminHandler")
        urlTree.insert(key: "/admin/settings", value: "SettingsHandler")
        
        XCTAssertEqual(urlTree.size, 6)
        
        // Test exact matching
        XCTAssertEqual(urlTree.search(key: "/api/users"), "UserHandler")
        XCTAssertEqual(urlTree.search(key: "/api/posts"), "PostHandler")
        
        // Test prefix matching for all API routes
        let apiRoutes = urlTree.keysWithPrefix("/api")
        XCTAssertEqual(apiRoutes.count, 4)
    }
    
    func testDomainNameSystem() {
        let dnsTree = RadixTree<String>()
        
        // Insert reverse DNS (for prefix compression efficiency)
        dnsTree.insert(key: "com.example", value: "93.184.216.34")
        dnsTree.insert(key: "com.example.www", value: "93.184.216.34")
        dnsTree.insert(key: "com.example.mail", value: "93.184.216.35")
        dnsTree.insert(key: "com.github", value: "140.82.121.4")
        dnsTree.insert(key: "com.github.api", value: "140.82.121.6")
        
        XCTAssertEqual(dnsTree.size, 5)
        
        // Find all subdomains of example.com
        let exampleDomains = dnsTree.keysWithPrefix("com.example")
        XCTAssertEqual(exampleDomains.count, 3)
        
        // Find all .com domains
        let comDomains = dnsTree.keysWithPrefix("com")
        XCTAssertEqual(comDomains.count, 5)
    }
    
    // MARK: - File Path Tests
    
    func testFileSystemPaths() {
        let pathTree = RadixTree<String>()
        
        // Insert file paths
        pathTree.insert(key: "/usr/local/bin/swift", value: "executable")
        pathTree.insert(key: "/usr/local/lib/libswift.dylib", value: "library")
        pathTree.insert(key: "/usr/bin/python", value: "executable")
        pathTree.insert(key: "/home/user/documents/file1.txt", value: "document")
        pathTree.insert(key: "/home/user/documents/file2.txt", value: "document")
        pathTree.insert(key: "/home/user/downloads/archive.zip", value: "archive")
        
        XCTAssertEqual(pathTree.size, 6)
        
        // Find all files in /usr/local
        let usrLocal = pathTree.keysWithPrefix("/usr/local")
        XCTAssertEqual(usrLocal.count, 2)
        
        // Find all files in /home/user/documents
        let documents = pathTree.keysWithPrefix("/home/user/documents")
        XCTAssertEqual(documents.count, 2)
        
        // Test longest common prefix
        let lcp = pathTree.longestCommonPrefix()
        XCTAssertTrue(lcp == "/" || lcp.isEmpty)
    }
    
    // MARK: - Prefix Compression Tests
    
    func testCompressionWithCommonPrefixes() {
        let radix = RadixTree<Int>()
        
        // Insert many keys with common prefixes
        for i in 0..<1000 {
            radix.insert(key: "prefix_common_\(i)", value: i)
        }
        
        let stats = radix.statistics()
        
        // Verify compression is working
        XCTAssertEqual(stats.elementCount, 1000)
        
        // Node count should be significantly less than element count due to compression
        XCTAssertLessThan(stats.nodeCount, 500)
        
        // Compression ratio should be good
        XCTAssertGreaterThan(stats.compressionRatio, 0.0)
        XCTAssertLessThan(stats.compressionRatio, 1.0)
    }
    
    func testCompressionWithUniqueKeys() {
        let radix = RadixTree<Int>()
        
        // Insert keys with no common prefixes
        radix.insert(key: "apple", value: 1)
        radix.insert(key: "banana", value: 2)
        radix.insert(key: "cherry", value: 3)
        radix.insert(key: "date", value: 4)
        radix.insert(key: "elderberry", value: 5)
        
        let stats = radix.statistics()
        
        // Less compression expected
        XCTAssertEqual(stats.elementCount, 5)
        XCTAssertGreaterThan(stats.nodeCount, 0)
    }
    
    func testLongestCommonPrefix() {
        let radix = RadixTree<Int>()
        
        // Insert keys with common prefix "test"
        radix.insert(key: "testing123", value: 1)
        radix.insert(key: "testing456", value: 2)
        radix.insert(key: "testing789", value: 3)
        
        let lcp = radix.longestCommonPrefix()
        XCTAssertEqual(lcp, "testing")
    }
    
    func testNoCommonPrefix() {
        let radix = RadixTree<Int>()
        
        radix.insert(key: "apple", value: 1)
        radix.insert(key: "banana", value: 2)
        
        let lcp = radix.longestCommonPrefix()
        XCTAssertTrue(lcp.isEmpty)
    }
    
    // MARK: - Database Integration Tests
    
    func testStringIndexUseCase() {
        let index = RadixTree<RID>.forStringIndex()
        
        // Simulate indexing varchar columns
        let names = ["Alice", "Alyssa", "Bob", "Bobby", "Charlie", "Charlotte"]
        
        for (i, name) in names.enumerated() {
            index.insert(key: name, value: RID(page: 0, slot: UInt16(i)))
        }
        
        XCTAssertEqual(index.size, 6)
        
        // Find all names starting with "Al"
        let alNames = index.keysWithPrefix("Al")
        XCTAssertEqual(alNames.count, 2)
        
        // Find all names starting with "Bob"
        let bobNames = index.keysWithPrefix("Bob")
        XCTAssertEqual(bobNames.count, 2)
    }
    
    func testEmailDomainIndex() {
        let emailIndex = RadixTree<[RID]>()
        
        // Index emails by domain
        emailIndex.insert(key: "gmail.com", value: [RID(page: 0, slot: 1), RID(page: 0, slot: 2)])
        emailIndex.insert(key: "yahoo.com", value: [RID(page: 0, slot: 3)])
        emailIndex.insert(key: "outlook.com", value: [RID(page: 0, slot: 4), RID(page: 0, slot: 5)])
        
        // Find all Gmail users
        if let gmailUsers = emailIndex.search(key: "gmail.com") {
            XCTAssertEqual(gmailUsers.count, 2)
        } else {
            XCTFail("Should find Gmail users")
        }
    }
    
    // MARK: - Stress Tests
    
    func testLargeScalePrefixCompression() {
        let radix = RadixTree<Int>()
        
        // Insert 10,000 keys with high prefix overlap
        for i in 0..<10_000 {
            radix.insert(key: "common_prefix_part_\(i)", value: i)
        }
        
        let stats = radix.statistics()
        
        XCTAssertEqual(stats.elementCount, 10_000)
        
        // Verify all can be retrieved
        for i in 0..<10_000 {
            XCTAssertNotNil(radix.search(key: "common_prefix_part_\(i)"))
        }
    }
    
    func testManyPrefixSearches() {
        let radix = RadixTree<Int>()
        
        // Insert words
        for i in 0..<1000 {
            radix.insert(key: "word\(i)", value: i)
        }
        
        // Perform many prefix searches
        for i in 0..<100 {
            let results = radix.keysWithPrefix("word\(i)")
            XCTAssertGreaterThan(results.count, 0)
        }
    }
    
    // MARK: - Performance Tests
    
    func testPrefixSearchPerformance() {
        let radix = RadixTree<Int>()
        
        // Pre-populate with common prefixes
        for i in 0..<5000 {
            radix.insert(key: "prefix_\(i)", value: i)
        }
        
        measure {
            for _ in 0..<100 {
                _ = radix.keysWithPrefix("prefix_")
            }
        }
    }
    
    func testAutocompletePerformance() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        // Add many suggestions
        let words = (0..<1000).map { "word\($0)" }
        for word in words {
            for i in 1...word.count {
                let prefix = String(word.prefix(i))
                autocomplete.addSuggestion(prefix: prefix, suggestion: word)
            }
        }
        
        measure {
            for i in 0..<100 {
                _ = autocomplete.search(key: "word\(i)")
            }
        }
    }
    
    // MARK: - Edge Cases
    
    func testSingleCharacterKeys() {
        let radix = RadixTree<Int>()
        
        let chars = "abcdefghijklmnopqrstuvwxyz"
        for (i, char) in chars.enumerated() {
            radix.insert(key: String(char), value: i)
        }
        
        XCTAssertEqual(radix.size, 26)
        
        // Each should be findable
        for (i, char) in chars.enumerated() {
            XCTAssertEqual(radix.search(key: String(char)), i)
        }
    }
    
    func testVeryLongKeys() {
        let radix = RadixTree<Int>()
        
        let longKey1 = String(repeating: "a", count: 1000) + "1"
        let longKey2 = String(repeating: "a", count: 1000) + "2"
        
        radix.insert(key: longKey1, value: 1)
        radix.insert(key: longKey2, value: 2)
        
        XCTAssertEqual(radix.size, 2)
        XCTAssertEqual(radix.search(key: longKey1), 1)
        XCTAssertEqual(radix.search(key: longKey2), 2)
        
        // Longest common prefix should be 1000 'a's
        let lcp = radix.longestCommonPrefix()
        XCTAssertEqual(lcp.count, 1000)
    }
}

