#!/bin/bash
#
# Script to run Group Commit benchmarks
#

echo "═══════════════════════════════════════════════════════════"
echo "  Colibrì-DB Group Commit Benchmarks"
echo "═══════════════════════════════════════════════════════════"
echo ""

# Make sure we're in the right directory
cd "$(dirname "$0")"

# Build first
echo "Building benchmarks..."
swift build -c release 2>&1 | tail -5

if [ $? -ne 0 ]; then
    echo "❌ Build failed!"
    exit 1
fi

echo "✅ Build successful!"
echo ""

# Run the Swift code to execute our benchmarks
swift run -c release benchmarks <<'EOF'
import ColibriCore
import Foundation

// Run all Group Commit benchmarks
do {
    print("\n")
    print("Running Group Commit Performance Tests...")
    print("")
    
    // 1. Basic comparison (with vs without)
    try BenchmarkCLI.benchmarkGroupCommit()
    
    // 2. Concurrent workload
    try BenchmarkCLI.benchmarkConcurrentGroupCommit()
    
    // 3. Batch size tuning
    try BenchmarkCLI.benchmarkGroupCommitBatchSizes()
    
    // 4. Stress test
    try BenchmarkCLI.stressTestGroupCommit()
    
    print("\n")
    print("═══════════════════════════════════════════════════════════")
    print("  All Group Commit Benchmarks Complete!")
    print("═══════════════════════════════════════════════════════════")
    
} catch {
    print("❌ Benchmark error: \(error)")
    exit(1)
}
EOF

