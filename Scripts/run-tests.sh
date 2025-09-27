#!/bin/bash

# ColibrìDB Test Runner Script
# Comprehensive test suite for all ColibrìDB functionality

set -e

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
TESTS_DIR="$DEV_DIR/tests"
REPORTS_DIR="$DEV_DIR/reports"
LOGS_DIR="$DEV_DIR/logs"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Test configuration
TEST_CONFIG=""
VERBOSE=false
COVERAGE=false
PARALLEL=false
STRESS_TEST=false

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
            TEST_CONFIG="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --coverage)
            COVERAGE=true
            shift
            ;;
        --parallel)
            PARALLEL=true
            shift
            ;;
        --stress)
            STRESS_TEST=true
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --config FILE     Test configuration file"
            echo "  --verbose         Verbose output"
            echo "  --coverage        Generate coverage report"
            echo "  --parallel        Run tests in parallel"
            echo "  --stress          Include stress tests"
            echo "  --help            Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Default configuration
if [ -z "$TEST_CONFIG" ]; then
    TEST_CONFIG="$DEV_DIR/configs/colibridb-test.conf.json"
fi

# Test results tracking
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Function to run a test
run_test() {
    local test_name="$1"
    local test_command="$2"
    local test_type="$3"
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    log "Running $test_type test: $test_name"
    
    local start_time=$(date +%s)
    local test_output
    local test_exit_code
    
    if [ "$VERBOSE" = true ]; then
        test_output=$(eval "$test_command" 2>&1)
        test_exit_code=$?
    else
        test_output=$(eval "$test_command" 2>&1)
        test_exit_code=$?
    fi
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    if [ $test_exit_code -eq 0 ]; then
        PASSED_TESTS=$((PASSED_TESTS + 1))
        success "$test_name passed (${duration}s)"
        if [ "$VERBOSE" = true ]; then
            echo "$test_output"
        fi
    else
        FAILED_TESTS=$((FAILED_TESTS + 1))
        error "$test_name failed (${duration}s)"
        echo "$test_output"
    fi
    
    # Log test result
    echo "$(date +'%Y-%m-%d %H:%M:%S'),$test_name,$test_type,$test_exit_code,$duration" >> "$REPORTS_DIR/test-results/test-results.csv"
}

# Unit Tests
run_unit_tests() {
    log "Running unit tests..."
    
    # Swift unit tests
    run_test "Swift Unit Tests" "cd '$PROJECT_ROOT' && swift test --configuration release" "unit"
    
    # CLI functionality tests
    run_test "CLI Help Test" ".build/release/coldb --help" "unit"
    run_test "CLI Version Test" ".build/release/coldb --version" "unit"
    run_test "Dev CLI Help Test" ".build/release/coldb-dev --help" "unit"
    
    # Configuration tests
    run_test "Config Validation Test" ".build/release/coldb --config '$TEST_CONFIG' --validate" "unit"
}

# Integration Tests
run_integration_tests() {
    log "Running integration tests..."
    
    # Database creation and management
    run_test "Database Creation" ".build/release/coldb --config '$TEST_CONFIG' --execute 'CREATE DATABASE test_integration;'" "integration"
    run_test "Database Listing" ".build/release/coldb --config '$TEST_CONFIG' --execute 'SHOW DATABASES;'" "integration"
    run_test "Database Deletion" ".build/release/coldb --config '$TEST_CONFIG' --execute 'DROP DATABASE test_integration;'" "integration"
    
    # Table operations
    run_test "Table Creation" ".build/release/coldb --config '$TEST_CONFIG' --execute 'CREATE TABLE test_table (id INTEGER PRIMARY KEY, name VARCHAR(100));'" "integration"
    run_test "Table Listing" ".build/release/coldb --config '$TEST_CONFIG' --execute 'SHOW TABLES;'" "integration"
    run_test "Table Schema" ".build/release/coldb --config '$TEST_CONFIG' --execute 'DESCRIBE test_table;'" "integration"
    run_test "Table Deletion" ".build/release/coldb --config '$TEST_CONFIG' --execute 'DROP TABLE test_table;'" "integration"
    
    # Data operations
    run_test "Data Insertion" ".build/release/coldb --config '$TEST_CONFIG' --execute 'CREATE TABLE test_data (id INTEGER PRIMARY KEY, value VARCHAR(100)); INSERT INTO test_data VALUES (1, \"test\");'" "integration"
    run_test "Data Selection" ".build/release/coldb --config '$TEST_CONFIG' --execute 'SELECT * FROM test_data;'" "integration"
    run_test "Data Update" ".build/release/coldb --config '$TEST_CONFIG' --execute 'UPDATE test_data SET value = \"updated\" WHERE id = 1;'" "integration"
    run_test "Data Deletion" ".build/release/coldb --config '$TEST_CONFIG' --execute 'DELETE FROM test_data WHERE id = 1;'" "integration"
    run_test "Data Cleanup" ".build/release/coldb --config '$TEST_CONFIG' --execute 'DROP TABLE test_data;'" "integration"
}

# Performance Tests
run_performance_tests() {
    log "Running performance tests..."
    
    # Query performance
    run_test "Query Performance Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\benchmark sql --iterations 1000'" "performance"
    
    # Memory performance
    run_test "Memory Performance Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\benchmark memory --iterations 100'" "performance"
    
    # Index performance
    run_test "Index Performance Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\benchmark constraints --iterations 1000'" "performance"
    
    # Data type performance
    run_test "Data Type Performance Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\benchmark types --iterations 10000'" "performance"
}

# Stress Tests
run_stress_tests() {
    if [ "$STRESS_TEST" = false ]; then
        return
    fi
    
    log "Running stress tests..."
    
    # High load test
    run_test "High Load Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\test stress --duration 60'" "stress"
    
    # Memory leak test
    run_test "Memory Leak Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\test memory --duration 300'" "stress"
    
    # Concurrent access test
    run_test "Concurrent Access Test" ".build/release/coldb-dev --config '$TEST_CONFIG' --execute '\\test concurrent --threads 10 --duration 60'" "stress"
}

# Server Tests
run_server_tests() {
    log "Running server tests..."
    
    # Start server
    log "Starting server for testing..."
    .build/release/colibri-server --config "$TEST_CONFIG" &
    SERVER_PID=$!
    sleep 5
    
    # Health check
    run_test "Server Health Check" "curl -f http://localhost:8080/health" "server"
    
    # API tests
    run_test "Database API Test" "curl -f -X POST http://localhost:8080/api/databases -d '{\"name\":\"test_api\"}'" "server"
    run_test "Table API Test" "curl -f -X POST http://localhost:8080/api/databases/test_api/tables -d '{\"name\":\"test_table\",\"schema\":{\"id\":\"INTEGER\",\"name\":\"VARCHAR(100)\"}}'" "server"
    run_test "Query API Test" "curl -f -X POST http://localhost:8080/api/query -d '{\"query\":\"SELECT 1 as test\"}'" "server"
    
    # Stop server
    kill $SERVER_PID 2>/dev/null || true
    sleep 2
}

# Coverage Tests
run_coverage_tests() {
    if [ "$COVERAGE" = false ]; then
        return
    fi
    
    log "Running coverage tests..."
    
    # Generate coverage data
    run_test "Coverage Generation" "cd '$PROJECT_ROOT' && swift test --enable-code-coverage" "coverage"
    
    # Generate coverage report
    run_test "Coverage Report" "cd '$PROJECT_ROOT' && xcrun llvm-cov show .build/debug/ColibriCorePackageTests.xctest/Contents/MacOS/ColibriCorePackageTests -instr-profile .build/debug/codecov/default.profdata" "coverage"
}

# Main test execution
main() {
    log "Starting ColibrìDB test suite..."
    log "Configuration: $TEST_CONFIG"
    log "Verbose: $VERBOSE"
    log "Coverage: $COVERAGE"
    log "Parallel: $PARALLEL"
    log "Stress: $STRESS_TEST"
    
    # Create test results directory
    mkdir -p "$REPORTS_DIR/test-results"
    
    # Initialize test results CSV
    echo "timestamp,test_name,test_type,exit_code,duration" > "$REPORTS_DIR/test-results/test-results.csv"
    
    local start_time=$(date +%s)
    
    # Run test suites
    run_unit_tests
    run_integration_tests
    run_performance_tests
    run_stress_tests
    run_server_tests
    run_coverage_tests
    
    local end_time=$(date +%s)
    local total_duration=$((end_time - start_time))
    
    # Generate summary
    log "Test suite completed in ${total_duration}s"
    log "Total tests: $TOTAL_TESTS"
    log "Passed: $PASSED_TESTS"
    log "Failed: $FAILED_TESTS"
    log "Skipped: $SKIPPED_TESTS"
    
    # Calculate success rate
    local success_rate=0
    if [ $TOTAL_TESTS -gt 0 ]; then
        success_rate=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    fi
    
    log "Success rate: ${success_rate}%"
    
    # Generate test report
    cat > "$REPORTS_DIR/test-results/test-summary.json" << EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "duration": $total_duration,
  "total_tests": $TOTAL_TESTS,
  "passed_tests": $PASSED_TESTS,
  "failed_tests": $FAILED_TESTS,
  "skipped_tests": $SKIPPED_TESTS,
  "success_rate": $success_rate,
  "configuration": "$TEST_CONFIG",
  "verbose": $VERBOSE,
  "coverage": $COVERAGE,
  "parallel": $PARALLEL,
  "stress": $STRESS_TEST
}
EOF
    
    if [ $FAILED_TESTS -eq 0 ]; then
        success "All tests passed!"
        exit 0
    else
        error "$FAILED_TESTS tests failed!"
        exit 1
    fi
}

# Run main function
main "$@"
