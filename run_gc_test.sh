#!/bin/bash

cd "$(dirname "$0")"

echo "═══════════════════════════════════════════════════════════"
echo "  Colibrì-DB Group Commit Performance Tests"
echo "═══════════════════════════════════════════════════════════"
echo ""

# Create a simple test program
cat > /tmp/gc_test_main.swift << 'EOF'
import ColibriCore
import Foundation

do {
    print("\n🧪 Test 1: Basic Group Commit Comparison\n")
    try BenchmarkCLI.benchmarkGroupCommit()
    
    print("\n\n🧪 Test 2: Concurrent Group Commit\n")
    try BenchmarkCLI.benchmarkConcurrentGroupCommit()
    
    print("\n✅ All tests completed successfully!\n")
} catch {
    print("❌ Error: \(error)")
    exit(1)
}
EOF

# Run using the benchmarks executable directly
.build/release/benchmarks << 'BENCH_EOF'
gc
BENCH_EOF

