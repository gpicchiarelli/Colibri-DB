#!/bin/bash

# ColibrìDB Benchmark Runner Script
# Comprehensive benchmark suite for performance testing

set -e

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
REPORTS_DIR="$DEV_DIR/reports"
LOGS_DIR="$DEV_DIR/logs"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Benchmark configuration
BENCHMARK_CONFIG=""
ITERATIONS=1000
DURATION=60
THREADS=4
VERBOSE=false
EXPORT_FORMAT="json"

# Functions
log() {
    echo -e "${BLUE}[$(date +'%Y-%m-%d %H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}[$(date +'%Y-%m-%d %H:%M:%S')] ✓${NC} $1"
}

warning() {
    echo -e "${YELLOW}[$(date +'%Y-%m-%d %H:%M:%S')] ⚠${NC} $1"
}

error() {
    echo -e "${RED}[$(date +'%Y-%m-%d %H:%M:%S')] ✗${NC} $1"
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --config)
            BENCHMARK_CONFIG="$2"
            shift 2
            ;;
        --iterations)
            ITERATIONS="$2"
            shift 2
            ;;
        --duration)
            DURATION="$2"
            shift 2
            ;;
        --threads)
            THREADS="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --format)
            EXPORT_FORMAT="$2"
            shift 2
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --config FILE      Benchmark configuration file"
            echo "  --iterations N     Number of iterations (default: 1000)"
            echo "  --duration N       Duration in seconds (default: 60)"
            echo "  --threads N        Number of threads (default: 4)"
            echo "  --verbose          Verbose output"
            echo "  --format FORMAT    Export format (json|csv|prometheus)"
            echo "  --help             Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Default configuration
if [ -z "$BENCHMARK_CONFIG" ]; then
    BENCHMARK_CONFIG="$DEV_DIR/configs/colibridb-perf.conf.json"
fi

# Benchmark results
# Note: Using temporary files instead of associative arrays for macOS compatibility BENCHMARK_RESULTS

# Function to run a benchmark
run_benchmark() {
    local benchmark_name="$1"
    local benchmark_command="$2"
    local benchmark_type="$3"
    
    log "Running benchmark: $benchmark_name"
    
    local start_time=$(date +%s%3N)
    local benchmark_output
    local benchmark_exit_code
    
    if [ "$VERBOSE" = true ]; then
        benchmark_output=$(eval "$benchmark_command" 2>&1)
        benchmark_exit_code=$?
    else
        benchmark_output=$(eval "$benchmark_command" 2>&1)
        benchmark_exit_code=$?
    fi
    
    local end_time=$(date +%s%3N)
    local duration=$((end_time - start_time))
    
    if [ $benchmark_exit_code -eq 0 ]; then
        success "$benchmark_name completed (${duration}ms)"
        
        # Extract metrics from output
        local throughput=$(echo "$benchmark_output" | grep -o 'throughput: [0-9.]*' | cut -d' ' -f2 || echo "0")
        local latency=$(echo "$benchmark_output" | grep -o 'latency: [0-9.]*' | cut -d' ' -f2 || echo "0")
        local memory=$(echo "$benchmark_output" | grep -o 'memory: [0-9.]*' | cut -d' ' -f2 || echo "0")
        
        # Store results
        BENCHMARK_RESULTS["${benchmark_name}_throughput"]="$throughput"
        BENCHMARK_RESULTS["${benchmark_name}_latency"]="$latency"
        BENCHMARK_RESULTS["${benchmark_name}_memory"]="$memory"
        BENCHMARK_RESULTS["${benchmark_name}_duration"]="$duration"
        
        if [ "$VERBOSE" = true ]; then
            echo "$benchmark_output"
        fi
    else
        error "$benchmark_name failed"
        echo "$benchmark_output"
    fi
    
    # Log benchmark result
    echo "$(date +'%Y-%m-%d %H:%M:%S'),$benchmark_name,$benchmark_type,$benchmark_exit_code,$duration,$throughput,$latency,$memory" >> "$REPORTS_DIR/benchmarks/benchmark-results.csv"
}

# SQL Performance Benchmarks
run_sql_benchmarks() {
    log "Running SQL performance benchmarks..."
    
    # Simple SELECT benchmark
    run_benchmark "SELECT Simple" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"SELECT 1\" --iterations $ITERATIONS'" "sql"
    
    # Complex SELECT benchmark
    run_benchmark "SELECT Complex" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"SELECT * FROM users WHERE age > 25 AND age < 50\" --iterations $ITERATIONS'" "sql"
    
    # INSERT benchmark
    run_benchmark "INSERT Single" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"INSERT INTO test_table VALUES (?, ?)\" --iterations $ITERATIONS'" "sql"
    
    # UPDATE benchmark
    run_benchmark "UPDATE Single" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"UPDATE test_table SET value = ? WHERE id = ?\" --iterations $ITERATIONS'" "sql"
    
    # DELETE benchmark
    run_benchmark "DELETE Single" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"DELETE FROM test_table WHERE id = ?\" --iterations $ITERATIONS'" "sql"
    
    # JOIN benchmark
    run_benchmark "JOIN Query" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"SELECT u.name, p.name FROM users u JOIN orders o ON u.id = o.user_id JOIN products p ON o.product_id = p.id\" --iterations $ITERATIONS'" "sql"
    
    # Aggregate benchmark
    run_benchmark "Aggregate Query" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark sql --query \"SELECT COUNT(*), AVG(age), MAX(age), MIN(age) FROM users\" --iterations $ITERATIONS'" "sql"
}

# Memory Performance Benchmarks
run_memory_benchmarks() {
    log "Running memory performance benchmarks..."
    
    # Memory allocation benchmark
    run_benchmark "Memory Allocation" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark memory --operation allocation --iterations $ITERATIONS'" "memory"
    
    # Memory deallocation benchmark
    run_benchmark "Memory Deallocation" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark memory --operation deallocation --iterations $ITERATIONS'" "memory"
    
    # Memory copy benchmark
    run_benchmark "Memory Copy" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark memory --operation copy --iterations $ITERATIONS'" "memory"
    
    # Memory move benchmark
    run_benchmark "Memory Move" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark memory --operation move --iterations $ITERATIONS'" "memory"
}

# Index Performance Benchmarks
run_index_benchmarks() {
    log "Running index performance benchmarks..."
    
    # Hash index benchmark
    run_benchmark "Hash Index Lookup" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type hash --operation lookup --iterations $ITERATIONS'" "index"
    
    # B-Tree index benchmark
    run_benchmark "B-Tree Index Lookup" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type btree --operation lookup --iterations $ITERATIONS'" "index"
    
    # ART index benchmark
    run_benchmark "ART Index Lookup" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type art --operation lookup --iterations $ITERATIONS'" "index"
    
    # Index range scan benchmark
    run_benchmark "Index Range Scan" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type btree --operation range --iterations $ITERATIONS'" "index"
    
    # Index insertion benchmark
    run_benchmark "Index Insertion" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type hash --operation insert --iterations $ITERATIONS'" "index"
    
    # Index deletion benchmark
    run_benchmark "Index Deletion" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark index --type hash --operation delete --iterations $ITERATIONS'" "index"
}

# Constraint Performance Benchmarks
run_constraint_benchmarks() {
    log "Running constraint performance benchmarks..."
    
    # Primary key constraint benchmark
    run_benchmark "Primary Key Constraint" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark constraints --type primary_key --iterations $ITERATIONS'" "constraint"
    
    # Unique constraint benchmark
    run_benchmark "Unique Constraint" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark constraints --type unique --iterations $ITERATIONS'" "constraint"
    
    # Check constraint benchmark
    run_benchmark "Check Constraint" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark constraints --type check --iterations $ITERATIONS'" "constraint"
    
    # Foreign key constraint benchmark
    run_benchmark "Foreign Key Constraint" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark constraints --type foreign_key --iterations $ITERATIONS'" "constraint"
    
    # Not null constraint benchmark
    run_benchmark "Not Null Constraint" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark constraints --type not_null --iterations $ITERATIONS'" "constraint"
}

# Data Type Performance Benchmarks
run_datatype_benchmarks() {
    log "Running data type performance benchmarks..."
    
    # Integer operations benchmark
    run_benchmark "Integer Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type integer --iterations $ITERATIONS'" "datatype"
    
    # String operations benchmark
    run_benchmark "String Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type string --iterations $ITERATIONS'" "datatype"
    
    # Decimal operations benchmark
    run_benchmark "Decimal Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type decimal --iterations $ITERATIONS'" "datatype"
    
    # Date operations benchmark
    run_benchmark "Date Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type date --iterations $ITERATIONS'" "datatype"
    
    # Boolean operations benchmark
    run_benchmark "Boolean Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type boolean --iterations $ITERATIONS'" "datatype"
    
    # JSON operations benchmark
    run_benchmark "JSON Operations" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark types --type json --iterations $ITERATIONS'" "datatype"
}

# Transaction Performance Benchmarks
run_transaction_benchmarks() {
    log "Running transaction performance benchmarks..."
    
    # Single transaction benchmark
    run_benchmark "Single Transaction" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark transaction --type single --iterations $ITERATIONS'" "transaction"
    
    # Batch transaction benchmark
    run_benchmark "Batch Transaction" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark transaction --type batch --iterations $ITERATIONS'" "transaction"
    
    # Concurrent transaction benchmark
    run_benchmark "Concurrent Transaction" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark transaction --type concurrent --threads $THREADS --iterations $ITERATIONS'" "transaction"
    
    # Long transaction benchmark
    run_benchmark "Long Transaction" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark transaction --type long --duration $DURATION'" "transaction"
}

# I/O Performance Benchmarks
run_io_benchmarks() {
    log "Running I/O performance benchmarks..."
    
    # Sequential read benchmark
    run_benchmark "Sequential Read" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark io --operation sequential_read --iterations $ITERATIONS'" "io"
    
    # Sequential write benchmark
    run_benchmark "Sequential Write" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark io --operation sequential_write --iterations $ITERATIONS'" "io"
    
    # Random read benchmark
    run_benchmark "Random Read" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark io --operation random_read --iterations $ITERATIONS'" "io"
    
    # Random write benchmark
    run_benchmark "Random Write" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark io --operation random_write --iterations $ITERATIONS'" "io"
    
    # WAL performance benchmark
    run_benchmark "WAL Performance" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark io --operation wal --iterations $ITERATIONS'" "io"
}

# Stress Benchmarks
run_stress_benchmarks() {
    log "Running stress benchmarks..."
    
    # High load benchmark
    run_benchmark "High Load" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark stress --type high_load --duration $DURATION --threads $THREADS'" "stress"
    
    # Memory pressure benchmark
    run_benchmark "Memory Pressure" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark stress --type memory_pressure --duration $DURATION'" "stress"
    
    # CPU intensive benchmark
    run_benchmark "CPU Intensive" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark stress --type cpu_intensive --duration $DURATION --threads $THREADS'" "stress"
    
    # I/O intensive benchmark
    run_benchmark "I/O Intensive" ".build/release/coldb-dev --config '$BENCHMARK_CONFIG' --execute '\\benchmark stress --type io_intensive --duration $DURATION'" "stress"
}

# Export benchmark results
export_results() {
    log "Exporting benchmark results..."
    
    local timestamp=$(date +%Y%m%d_%H%M%S)
    local export_file="$REPORTS_DIR/benchmarks/benchmark-results-${timestamp}.${EXPORT_FORMAT}"
    
    case $EXPORT_FORMAT in
        json)
            # Generate JSON report
            cat > "$export_file" << EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "configuration": "$BENCHMARK_CONFIG",
  "iterations": $ITERATIONS,
  "duration": $DURATION,
  "threads": $THREADS,
  "results": {
EOF
            
            local first=true
            for key in "${!BENCHMARK_RESULTS[@]}"; do
                if [ "$first" = true ]; then
                    first=false
                else
                    echo "," >> "$export_file"
                fi
                echo "    \"$key\": \"${BENCHMARK_RESULTS[$key]}\"" >> "$export_file"
            done
            
            cat >> "$export_file" << EOF
  }
}
EOF
            ;;
        csv)
            # Generate CSV report
            echo "benchmark_name,metric,value" > "$export_file"
            for key in "${!BENCHMARK_RESULTS[@]}"; do
                local benchmark_name=$(echo "$key" | cut -d'_' -f1-2)
                local metric=$(echo "$key" | cut -d'_' -f3-)
                echo "$benchmark_name,$metric,${BENCHMARK_RESULTS[$key]}" >> "$export_file"
            done
            ;;
        prometheus)
            # Generate Prometheus metrics
            cat > "$export_file" << EOF
# HELP colibridb_benchmark_throughput Operations per second
# TYPE colibridb_benchmark_throughput gauge
EOF
            
            for key in "${!BENCHMARK_RESULTS[@]}"; do
                if [[ $key == *"_throughput" ]]; then
                    local benchmark_name=$(echo "$key" | sed 's/_throughput//')
                    echo "colibridb_benchmark_throughput{benchmark=\"$benchmark_name\"} ${BENCHMARK_RESULTS[$key]}" >> "$export_file"
                fi
            done
            
            cat >> "$export_file" << EOF

# HELP colibridb_benchmark_latency Latency in milliseconds
# TYPE colibridb_benchmark_latency gauge
EOF
            
            for key in "${!BENCHMARK_RESULTS[@]}"; do
                if [[ $key == *"_latency" ]]; then
                    local benchmark_name=$(echo "$key" | sed 's/_latency//')
                    echo "colibridb_benchmark_latency{benchmark=\"$benchmark_name\"} ${BENCHMARK_RESULTS[$key]}" >> "$export_file"
                fi
            done
            ;;
    esac
    
    success "Results exported to: $export_file"
}

# Main benchmark execution
main() {
    log "Starting ColibrìDB benchmark suite..."
    log "Configuration: $BENCHMARK_CONFIG"
    log "Iterations: $ITERATIONS"
    log "Duration: $DURATION"
    log "Threads: $THREADS"
    log "Export format: $EXPORT_FORMAT"
    
    # Create benchmark results directory
    mkdir -p "$REPORTS_DIR/benchmarks"
    
    # Initialize benchmark results CSV
    echo "timestamp,benchmark_name,benchmark_type,exit_code,duration,throughput,latency,memory" > "$REPORTS_DIR/benchmarks/benchmark-results.csv"
    
    local start_time=$(date +%s)
    
    # Run benchmark suites
    run_sql_benchmarks
    run_memory_benchmarks
    run_index_benchmarks
    run_constraint_benchmarks
    run_datatype_benchmarks
    run_transaction_benchmarks
    run_io_benchmarks
    run_stress_benchmarks
    
    local end_time=$(date +%s)
    local total_duration=$((end_time - start_time))
    
    # Export results
    export_results
    
    # Generate summary
    log "Benchmark suite completed in ${total_duration}s"
    log "Results exported in $EXPORT_FORMAT format"
    
    success "Benchmark suite completed successfully!"
}

# Run main function
main "$@"
