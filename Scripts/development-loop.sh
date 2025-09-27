#!/bin/bash

# ColibrìDB Development Loop Script
# Automated development and testing cycle

set -e

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
LOGS_DIR="$DEV_DIR/logs"
REPORTS_DIR="$DEV_DIR/reports"
DATA_DIR="$DEV_DIR/data"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
CYAN='\033[0;36m'
NC='\033[0m'

# Loop configuration
CONTINUOUS=false
ITERATIONS=1
INTERVAL=300
VERBOSE=false
CLEANUP_AFTER=true
GENERATE_REPORTS=true
NOTIFY_ON_FAILURE=true

# State tracking
CURRENT_ITERATION=0
TOTAL_FAILURES=0
TOTAL_SUCCESSES=0
START_TIME=$(date +%s)

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

info() {
    echo -e "${CYAN}[$(date +'%Y-%m-%d %H:%M:%S')] ℹ${NC} $1"
}

highlight() {
    echo -e "${PURPLE}[$(date +'%Y-%m-%d %H:%M:%S')] ★${NC} $1"
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --continuous)
            CONTINUOUS=true
            shift
            ;;
        --iterations)
            ITERATIONS="$2"
            shift 2
            ;;
        --interval)
            INTERVAL="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --no-cleanup)
            CLEANUP_AFTER=false
            shift
            ;;
        --no-reports)
            GENERATE_REPORTS=false
            shift
            ;;
        --no-notify)
            NOTIFY_ON_FAILURE=false
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --continuous        Run continuously"
            echo "  --iterations N      Number of iterations (default: 1)"
            echo "  --interval N        Interval between iterations in seconds (default: 300)"
            echo "  --verbose           Verbose output"
            echo "  --no-cleanup        Skip cleanup after each iteration"
            echo "  --no-reports        Skip report generation"
            echo "  --no-notify         Skip failure notifications"
            echo "  --help              Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Function to show banner
show_banner() {
    echo -e "${PURPLE}"
    echo "╔══════════════════════════════════════════════════════════════╗"
    echo "║                    ColibrìDB Development Loop                ║"
    echo "║                                                              ║"
    echo "║  Automated development, testing, and validation cycle       ║"
    echo "║                                                              ║"
    echo "╚══════════════════════════════════════════════════════════════╝"
    echo -e "${NC}"
}

# Function to show configuration
show_configuration() {
    log "Development Loop Configuration:"
    echo "  Project Root: $PROJECT_ROOT"
    echo "  Development Dir: $DEV_DIR"
    echo "  Continuous Mode: $CONTINUOUS"
    echo "  Iterations: $ITERATIONS"
    echo "  Interval: $INTERVAL seconds"
    echo "  Verbose: $VERBOSE"
    echo "  Cleanup After: $CLEANUP_AFTER"
    echo "  Generate Reports: $GENERATE_REPORTS"
    echo "  Notify on Failure: $NOTIFY_ON_FAILURE"
    echo ""
}

# Function to check prerequisites
check_prerequisites() {
    log "Checking prerequisites..."
    
    # Check if Swift is installed
    if ! command -v swift &> /dev/null; then
        error "Swift is not installed or not in PATH"
        exit 1
    fi
    
    # Check if jq is installed
    if ! command -v jq &> /dev/null; then
        warning "jq is not installed, some features may not work"
    fi
    
    # Check if curl is installed
    if ! command -v curl &> /dev/null; then
        error "curl is not installed"
        exit 1
    fi
    
    # Check if development environment exists
    if [ ! -d "$DEV_DIR" ]; then
        warning "Development environment not found, creating..."
        "$PROJECT_ROOT/Scripts/dev-environment.sh"
    fi
    
    success "Prerequisites check completed"
}

# Function to run a single iteration
run_iteration() {
    local iteration=$1
    local start_time=$(date +%s)
    
    highlight "Starting iteration $iteration"
    
    # Phase 1: Build
    log "Phase 1: Building project..."
    if ! build_project; then
        error "Build failed in iteration $iteration"
        return 1
    fi
    success "Build completed"
    
    # Phase 2: Start server
    log "Phase 2: Starting server..."
    local server_pid
    if ! start_server server_pid; then
        error "Server start failed in iteration $iteration"
        return 1
    fi
    success "Server started (PID: $server_pid)"
    
    # Phase 3: Run tests
    log "Phase 3: Running tests..."
    if ! run_tests; then
        error "Tests failed in iteration $iteration"
        stop_server $server_pid
        return 1
    fi
    success "Tests completed"
    
    # Phase 4: Run benchmarks
    log "Phase 4: Running benchmarks..."
    if ! run_benchmarks; then
        error "Benchmarks failed in iteration $iteration"
        stop_server $server_pid
        return 1
    fi
    success "Benchmarks completed"
    
    # Phase 5: Collect telemetry
    log "Phase 5: Collecting telemetry..."
    if ! collect_telemetry; then
        warning "Telemetry collection failed in iteration $iteration"
    else
        success "Telemetry collected"
    fi
    
    # Phase 6: Generate reports
    if [ "$GENERATE_REPORTS" = true ]; then
        log "Phase 6: Generating reports..."
        if ! generate_reports $iteration; then
            warning "Report generation failed in iteration $iteration"
        else
            success "Reports generated"
        fi
    fi
    
    # Phase 7: Stop server
    log "Phase 7: Stopping server..."
    if ! stop_server $server_pid; then
        warning "Server stop failed in iteration $iteration"
    else
        success "Server stopped"
    fi
    
    # Phase 8: Cleanup
    if [ "$CLEANUP_AFTER" = true ]; then
        log "Phase 8: Cleaning up..."
        if ! cleanup_environment; then
            warning "Cleanup failed in iteration $iteration"
        else
            success "Cleanup completed"
        fi
    fi
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    success "Iteration $iteration completed in ${duration}s"
    return 0
}

# Function to build project
build_project() {
    cd "$PROJECT_ROOT"
    
    # Clean previous build
    if [ "$VERBOSE" = true ]; then
        swift package clean
    else
        swift package clean > /dev/null 2>&1
    fi
    
    # Build project
    if [ "$VERBOSE" = true ]; then
        swift build --configuration release
    else
        swift build --configuration release > "$LOGS_DIR/build.log" 2>&1
    fi
    
    return $?
}

# Function to start server
start_server() {
    local -n server_pid_ref=$1
    
    cd "$PROJECT_ROOT"
    
    # Start server in background
    .build/release/colibri-server --config "$DEV_DIR/configs/colibridb-dev.conf.json" > "$LOGS_DIR/server.log" 2>&1 &
    server_pid_ref=$!
    
    # Wait for server to start
    local max_wait=30
    local wait_count=0
    
    while [ $wait_count -lt $max_wait ]; do
        if curl -s http://localhost:8080/health > /dev/null 2>&1; then
            return 0
        fi
        sleep 1
        wait_count=$((wait_count + 1))
    done
    
    return 1
}

# Function to stop server
stop_server() {
    local server_pid=$1
    
    if [ -n "$server_pid" ] && kill -0 $server_pid 2>/dev/null; then
        kill $server_pid
        sleep 2
        
        # Force kill if still running
        if kill -0 $server_pid 2>/dev/null; then
            kill -9 $server_pid
        fi
    fi
    
    return 0
}

# Function to run tests
run_tests() {
    cd "$PROJECT_ROOT"
    
    if [ "$VERBOSE" = true ]; then
        "$PROJECT_ROOT/Scripts/run-tests.sh" --config "$DEV_DIR/configs/colibridb-test.conf.json" --verbose
    else
        "$PROJECT_ROOT/Scripts/run-tests.sh" --config "$DEV_DIR/configs/colibridb-test.conf.json" > "$LOGS_DIR/tests.log" 2>&1
    fi
    
    return $?
}

# Function to run benchmarks
run_benchmarks() {
    cd "$PROJECT_ROOT"
    
    if [ "$VERBOSE" = true ]; then
        "$PROJECT_ROOT/Scripts/run-benchmarks.sh" --config "$DEV_DIR/configs/colibridb-perf.conf.json" --verbose
    else
        "$PROJECT_ROOT/Scripts/run-benchmarks.sh" --config "$DEV_DIR/configs/colibridb-perf.conf.json" > "$LOGS_DIR/benchmarks.log" 2>&1
    fi
    
    return $?
}

# Function to collect telemetry
collect_telemetry() {
    cd "$PROJECT_ROOT"
    
    if [ "$VERBOSE" = true ]; then
        "$PROJECT_ROOT/Scripts/collect-telemetry.sh" --output "$REPORTS_DIR/telemetry" --duration 60 --verbose
    else
        "$PROJECT_ROOT/Scripts/collect-telemetry.sh" --output "$REPORTS_DIR/telemetry" --duration 60 > "$LOGS_DIR/telemetry.log" 2>&1
    fi
    
    return $?
}

# Function to generate reports
generate_reports() {
    local iteration=$1
    
    cd "$PROJECT_ROOT"
    
    if [ "$VERBOSE" = true ]; then
        "$PROJECT_ROOT/Scripts/generate-report.sh" --cycle "iteration-$iteration" --output "$REPORTS_DIR/iteration-$iteration" --verbose
    else
        "$PROJECT_ROOT/Scripts/generate-report.sh" --cycle "iteration-$iteration" --output "$REPORTS_DIR/iteration-$iteration" > "$LOGS_DIR/reports.log" 2>&1
    fi
    
    return $?
}

# Function to cleanup environment
cleanup_environment() {
    cd "$PROJECT_ROOT"
    
    if [ "$VERBOSE" = true ]; then
        "$PROJECT_ROOT/Scripts/cleanup.sh" --data --logs --reports --verbose
    else
        "$PROJECT_ROOT/Scripts/cleanup.sh" --data --logs --reports > "$LOGS_DIR/cleanup.log" 2>&1
    fi
    
    return $?
}

# Function to show iteration summary
show_iteration_summary() {
    local iteration=$1
    local success=$2
    local duration=$3
    
    echo ""
    echo -e "${PURPLE}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${PURPLE}║                    Iteration $iteration Summary                    ║${NC}"
    echo -e "${PURPLE}╠══════════════════════════════════════════════════════════════╣${NC}"
    
    if [ $success -eq 0 ]; then
        echo -e "${PURPLE}║  Status: ${GREEN}SUCCESS${PURPLE}                                           ║${NC}"
        TOTAL_SUCCESSES=$((TOTAL_SUCCESSES + 1))
    else
        echo -e "${PURPLE}║  Status: ${RED}FAILURE${PURPLE}                                           ║${NC}"
        TOTAL_FAILURES=$((TOTAL_FAILURES + 1))
    fi
    
    echo -e "${PURPLE}║  Duration: ${CYAN}${duration}s${PURPLE}                                        ║${NC}"
    echo -e "${PURPLE}║  Total Successes: ${GREEN}$TOTAL_SUCCESSES${PURPLE}                                ║${NC}"
    echo -e "${PURPLE}║  Total Failures: ${RED}$TOTAL_FAILURES${PURPLE}                                 ║${NC}"
    echo -e "${PURPLE}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
}

# Function to show final summary
show_final_summary() {
    local end_time=$(date +%s)
    local total_duration=$((end_time - START_TIME))
    
    echo ""
    echo -e "${PURPLE}╔══════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${PURPLE}║                    Final Summary                            ║${NC}"
    echo -e "${PURPLE}╠══════════════════════════════════════════════════════════════╣${NC}"
    echo -e "${PURPLE}║  Total Iterations: ${CYAN}$CURRENT_ITERATION${PURPLE}                                ║${NC}"
    echo -e "${PURPLE}║  Total Duration: ${CYAN}${total_duration}s${PURPLE}                                 ║${NC}"
    echo -e "${PURPLE}║  Successes: ${GREEN}$TOTAL_SUCCESSES${PURPLE}                                      ║${NC}"
    echo -e "${PURPLE}║  Failures: ${RED}$TOTAL_FAILURES${PURPLE}                                       ║${NC}"
    
    if [ $CURRENT_ITERATION -gt 0 ]; then
        local success_rate=$((TOTAL_SUCCESSES * 100 / CURRENT_ITERATION))
        echo -e "${PURPLE}║  Success Rate: ${CYAN}${success_rate}%${PURPLE}                                    ║${NC}"
    fi
    
    echo -e "${PURPLE}╚══════════════════════════════════════════════════════════════╝${NC}"
    echo ""
}

# Function to send notification
send_notification() {
    local message="$1"
    
    if [ "$NOTIFY_ON_FAILURE" = true ]; then
        # Try to send system notification
        if command -v osascript &> /dev/null; then
            osascript -e "display notification \"$message\" with title \"ColibrìDB Development Loop\""
        fi
    fi
}

# Main execution
main() {
    show_banner
    show_configuration
    
    # Check prerequisites
    check_prerequisites
    
    # Create necessary directories
    mkdir -p "$LOGS_DIR"
    mkdir -p "$REPORTS_DIR"
    mkdir -p "$DATA_DIR"
    
    # Main loop
    if [ "$CONTINUOUS" = true ]; then
        log "Starting continuous development loop..."
        CURRENT_ITERATION=0
        
        while true; do
            CURRENT_ITERATION=$((CURRENT_ITERATION + 1))
            local iteration_start=$(date +%s)
            
            if run_iteration $CURRENT_ITERATION; then
                success "Iteration $CURRENT_ITERATION completed successfully"
            else
                error "Iteration $CURRENT_ITERATION failed"
                send_notification "Development loop iteration $CURRENT_ITERATION failed"
            fi
            
            local iteration_end=$(date +%s)
            local iteration_duration=$((iteration_end - iteration_start))
            
            show_iteration_summary $CURRENT_ITERATION $? $iteration_duration
            
            # Wait before next iteration
            if [ $INTERVAL -gt 0 ]; then
                log "Waiting $INTERVAL seconds before next iteration..."
                sleep $INTERVAL
            fi
        done
    else
        log "Starting $ITERATIONS iteration(s)..."
        
        for ((i=1; i<=ITERATIONS; i++)); do
            CURRENT_ITERATION=$i
            local iteration_start=$(date +%s)
            
            if run_iteration $i; then
                success "Iteration $i completed successfully"
            else
                error "Iteration $i failed"
                send_notification "Development loop iteration $i failed"
            fi
            
            local iteration_end=$(date +%s)
            local iteration_duration=$((iteration_end - iteration_start))
            
            show_iteration_summary $i $? $iteration_duration
            
            # Wait before next iteration (except for last one)
            if [ $i -lt $ITERATIONS ] && [ $INTERVAL -gt 0 ]; then
                log "Waiting $INTERVAL seconds before next iteration..."
                sleep $INTERVAL
            fi
        done
        
        show_final_summary
    fi
}

# Run main function
main "$@"
