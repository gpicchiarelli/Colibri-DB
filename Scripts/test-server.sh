#!/bin/bash

# ColibrìDB Server Test Script
# This script tests the ColibrìDB HTTP server API

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
SERVER_HOST="localhost"
SERVER_PORT="8080"
BASE_URL="http://$SERVER_HOST:$SERVER_PORT"

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to make HTTP request
make_request() {
    local method="$1"
    local endpoint="$2"
    local data="$3"
    local expected_status="$4"
    
    local url="$BASE_URL$endpoint"
    local response
    local status_code
    
    print_status "Testing $method $endpoint"
    
    if [[ -n "$data" ]]; then
        response=$(curl -s -w "\n%{http_code}" -X "$method" \
            -H "Content-Type: application/json" \
            -d "$data" \
            "$url")
    else
        response=$(curl -s -w "\n%{http_code}" -X "$method" "$url")
    fi
    
    status_code=$(echo "$response" | tail -n1)
    response_body=$(echo "$response" | head -n -1)
    
    if [[ "$status_code" == "$expected_status" ]]; then
        print_success "✓ $method $endpoint - Status: $status_code"
        echo "$response_body" | jq . 2>/dev/null || echo "$response_body"
    else
        print_error "✗ $method $endpoint - Expected: $expected_status, Got: $status_code"
        echo "$response_body"
        return 1
    fi
    
    echo ""
}

# Function to check if server is running
check_server() {
    print_status "Checking if server is running..."
    
    if curl -s "$BASE_URL/health" >/dev/null 2>&1; then
        print_success "Server is running on $BASE_URL"
        return 0
    else
        print_error "Server is not running on $BASE_URL"
        print_status "Please start the server first:"
        print_status "  sudo ./Scripts/install-service.sh start"
        return 1
    fi
}

# Function to test health endpoints
test_health_endpoints() {
    print_status "Testing health endpoints..."
    echo "================================"
    
    make_request "GET" "/health" "" "200"
    make_request "GET" "/status" "" "200"
    make_request "GET" "/info" "" "200"
}

# Function to test database operations
test_database_operations() {
    print_status "Testing database operations..."
    echo "=================================="
    
    make_request "GET" "/api/v1/databases" "" "200"
    
    make_request "POST" "/api/v1/databases" '{
        "name": "testdb"
    }' "201"
}

# Function to test table operations
test_table_operations() {
    print_status "Testing table operations..."
    echo "=============================="
    
    make_request "GET" "/api/v1/tables/default" "" "200"
    
    make_request "POST" "/api/v1/tables" '{
        "name": "users",
        "columns": [
            {"name": "id", "type": "int", "nullable": false},
            {"name": "name", "type": "string", "nullable": true},
            {"name": "email", "type": "string", "nullable": true}
        ]
    }' "201"
    
    make_request "DELETE" "/api/v1/tables/default/users" "" "200"
}

# Function to test query operations
test_query_operations() {
    print_status "Testing query operations..."
    echo "=============================="
    
    make_request "POST" "/api/v1/query" '{
        "sql": "SELECT * FROM users WHERE id > 1"
    }' "200"
}

# Function to test transaction operations
test_transaction_operations() {
    print_status "Testing transaction operations..."
    echo "===================================="
    
    # Begin transaction
    local begin_response
    begin_response=$(curl -s -X POST "$BASE_URL/api/v1/transactions/begin")
    local tid
    tid=$(echo "$begin_response" | jq -r '.transactionId')
    
    if [[ "$tid" != "null" && "$tid" != "" ]]; then
        print_success "✓ Transaction started - ID: $tid"
        
        # Commit transaction
        make_request "POST" "/api/v1/transactions/commit" "{
            \"transactionId\": $tid
        }" "200"
        
        # Begin another transaction
        begin_response=$(curl -s -X POST "$BASE_URL/api/v1/transactions/begin")
        tid=$(echo "$begin_response" | jq -r '.transactionId')
        
        # Rollback transaction
        make_request "POST" "/api/v1/transactions/rollback" "{
            \"transactionId\": $tid
        }" "200"
    else
        print_error "✗ Failed to start transaction"
    fi
    
    make_request "GET" "/api/v1/transactions" "" "200"
}

# Function to test index operations
test_index_operations() {
    print_status "Testing index operations..."
    echo "=============================="
    
    make_request "GET" "/api/v1/indexes/users" "" "200"
    
    make_request "POST" "/api/v1/indexes" '{
        "name": "users_id_idx",
        "table": "users",
        "columns": ["id"],
        "type": "BTREE"
    }' "201"
    
    make_request "DELETE" "/api/v1/indexes/users/users_id_idx" "" "200"
}

# Function to test monitoring operations
test_monitoring_operations() {
    print_status "Testing monitoring operations..."
    echo "==================================="
    
    make_request "GET" "/api/v1/monitoring/metrics" "" "200"
    make_request "GET" "/api/v1/monitoring/health" "" "200"
    make_request "GET" "/api/v1/monitoring/errors" "" "200"
}

# Function to test testing operations
test_testing_operations() {
    print_status "Testing testing operations..."
    echo "================================"
    
    make_request "POST" "/api/v1/testing/run" "" "200"
    make_request "POST" "/api/v1/testing/unit" "" "200"
    make_request "POST" "/api/v1/testing/integration" "" "200"
    make_request "POST" "/api/v1/testing/performance" "" "200"
}

# Function to test performance operations
test_performance_operations() {
    print_status "Testing performance operations..."
    echo "====================================="
    
    make_request "GET" "/api/v1/performance/metrics" "" "200"
    make_request "POST" "/api/v1/performance/benchmarks" "" "200"
}

# Function to run load test
run_load_test() {
    print_status "Running load test..."
    echo "======================"
    
    local concurrent_requests=10
    local total_requests=100
    
    print_status "Sending $total_requests requests with $concurrent_requests concurrent connections"
    
    # Use ab (Apache Bench) if available
    if command -v ab >/dev/null 2>&1; then
        ab -n $total_requests -c $concurrent_requests "$BASE_URL/health"
    else
        print_warning "Apache Bench not available, using curl for load test"
        
        # Simple load test with curl
        local success_count=0
        local error_count=0
        
        for i in $(seq 1 $total_requests); do
            if curl -s "$BASE_URL/health" >/dev/null 2>&1; then
                ((success_count++))
            else
                ((error_count++))
            fi
            
            if ((i % 10 == 0)); then
                print_status "Completed $i/$total_requests requests"
            fi
        done
        
        print_success "Load test completed: $success_count successful, $error_count failed"
    fi
}

# Function to run all tests
run_all_tests() {
    print_status "Running all API tests..."
    echo "============================"
    
    test_health_endpoints
    test_database_operations
    test_table_operations
    test_query_operations
    test_transaction_operations
    test_index_operations
    test_monitoring_operations
    test_testing_operations
    test_performance_operations
    
    print_success "All tests completed!"
}

# Function to show usage
show_usage() {
    echo "ColibrìDB Server Test Script"
    echo "============================"
    echo ""
    echo "Usage: $0 [command]"
    echo ""
    echo "Commands:"
    echo "  all          Run all tests (default)"
    echo "  health       Test health endpoints"
    echo "  database     Test database operations"
    echo "  table        Test table operations"
    echo "  query        Test query operations"
    echo "  transaction  Test transaction operations"
    echo "  index        Test index operations"
    echo "  monitoring   Test monitoring operations"
    echo "  testing      Test testing operations"
    echo "  performance  Test performance operations"
    echo "  load         Run load test"
    echo "  help         Show this help message"
    echo ""
    echo "Configuration:"
    echo "  Server: $BASE_URL"
    echo "  Host: $SERVER_HOST"
    echo "  Port: $SERVER_PORT"
}

# Main function
main() {
    # Check if server is running
    if ! check_server; then
        exit 1
    fi
    
    # Check if jq is available
    if ! command -v jq >/dev/null 2>&1; then
        print_warning "jq not found. Install it for better JSON output: brew install jq"
    fi
    
    # Parse command line arguments
    case "${1:-all}" in
        "all")
            run_all_tests
            ;;
        "health")
            test_health_endpoints
            ;;
        "database")
            test_database_operations
            ;;
        "table")
            test_table_operations
            ;;
        "query")
            test_query_operations
            ;;
        "transaction")
            test_transaction_operations
            ;;
        "index")
            test_index_operations
            ;;
        "monitoring")
            test_monitoring_operations
            ;;
        "testing")
            test_testing_operations
            ;;
        "performance")
            test_performance_operations
            ;;
        "load")
            run_load_test
            ;;
        "help"|"-h"|"--help")
            show_usage
            ;;
        *)
            print_error "Unknown command: $1"
            show_usage
            exit 1
            ;;
    esac
}

# Run main function
main "$@"
