#!/bin/bash
# Benchmark Suite Runner
echo "🧪 Running Comprehensive Benchmark Suite"
echo "========================================"
echo ""

RESULTS_FILE="benchmark_results_$(date +%Y%m%d_%H%M%S).txt"

run_bench() {
    local name=$1
    local iterations=$2
    echo "Testing: $name ($iterations ops)"
    .build/debug/benchmarks $iterations $name 2>&1 | grep -E "throughput_ops_s|latenza_ms:" | tee -a "$RESULTS_FILE"
    echo ""
}

# Core operations
echo "📊 CORE OPERATIONS"
echo "===================="
run_bench "heap-insert" 10000
run_bench "heap-scan" 1000
run_bench "heap-delete" 5000

# Index operations
echo "📇 INDEX OPERATIONS"
echo "===================="
run_bench "btree-lookup" 5000
run_bench "idx-hash-lookup" 10000
run_bench "idx-skiplist-lookup" 10000
run_bench "idx-btree-lookup" 10000

# Transaction operations
echo "💳 TRANSACTION OPERATIONS"
echo "=========================="
run_bench "tx-commit" 2000
run_bench "tx-rollback" 1000
run_bench "tx-contention" 5000

# WAL operations
echo "📝 WAL OPERATIONS"
echo "=================="
run_bench "wal-append-none" 5000
run_bench "fileheap-insert-wal-off" 2000

# Query operations
echo "🔍 QUERY OPERATIONS"
echo "===================="
run_bench "planner-join" 100
run_bench "planner-index-scan" 500

echo ""
echo "✅ Benchmark suite complete!"
echo "📄 Results saved to: $RESULTS_FILE"
