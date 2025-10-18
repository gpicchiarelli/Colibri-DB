import Foundation
import ColibriCore

print("═══════════════════════════════════════════════════════════")
print("  Colibrì-DB Group Commit Performance Tests")
print("═══════════════════════════════════════════════════════════")
print("")

do {
    // Test 1: Basic comparison
    try BenchmarkCLI.benchmarkGroupCommit()
    
    print("\n")
    print("─────────────────────────────────────────────────────────")
    print("")
    
    // Test 2: Concurrent workload  
    try BenchmarkCLI.benchmarkConcurrentGroupCommit()
    
    print("\n")
    print("═══════════════════════════════════════════════════════════")
    print("  Tests Complete!")
    print("═══════════════════════════════════════════════════════════")
    
} catch {
    print("❌ Error: \(error)")
    exit(1)
}

