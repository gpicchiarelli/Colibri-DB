#!/bin/bash

# ColibrìDB Telemetry Collection Script
# Comprehensive telemetry and monitoring data collection

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

# Telemetry configuration
OUTPUT_DIR=""
DURATION=300
INTERVAL=1
FORMAT="json"
VERBOSE=false
INCLUDE_LOGS=true
INCLUDE_METRICS=true
INCLUDE_PROFILING=true

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
        --output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --duration)
            DURATION="$2"
            shift 2
            ;;
        --interval)
            INTERVAL="$2"
            shift 2
            ;;
        --format)
            FORMAT="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --no-logs)
            INCLUDE_LOGS=false
            shift
            ;;
        --no-metrics)
            INCLUDE_METRICS=false
            shift
            ;;
        --no-profiling)
            INCLUDE_PROFILING=false
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --output DIR       Output directory for telemetry data"
            echo "  --duration N       Collection duration in seconds (default: 300)"
            echo "  --interval N       Collection interval in seconds (default: 1)"
            echo "  --format FORMAT    Output format (json|csv|prometheus)"
            echo "  --verbose          Verbose output"
            echo "  --no-logs          Skip log collection"
            echo "  --no-metrics       Skip metrics collection"
            echo "  --no-profiling     Skip profiling data"
            echo "  --help             Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Default output directory
if [ -z "$OUTPUT_DIR" ]; then
    OUTPUT_DIR="$REPORTS_DIR/telemetry/$(date +%Y%m%d_%H%M%S)"
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Telemetry data storage
# Note: Using temporary files instead of associative arrays for macOS compatibility

# Function to collect system metrics
collect_system_metrics() {
    local timestamp=$(date +%s)
    
    # CPU metrics
    local cpu_usage=$(top -l 1 | grep "CPU usage" | awk '{print $3}' | sed 's/%//')
    local cpu_user=$(top -l 1 | grep "CPU usage" | awk '{print $2}' | sed 's/%//')
    local cpu_sys=$(top -l 1 | grep "CPU usage" | awk '{print $4}' | sed 's/%//')
    local cpu_idle=$(top -l 1 | grep "CPU usage" | awk '{print $6}' | sed 's/%//')
    
    # Memory metrics
    local memory_total=$(sysctl -n hw.memsize)
    local memory_used=$(vm_stat | grep "Pages active" | awk '{print $3}' | sed 's/\.//')
    local memory_free=$(vm_stat | grep "Pages free" | awk '{print $3}' | sed 's/\.//')
    local memory_wired=$(vm_stat | grep "Pages wired down" | awk '{print $4}' | sed 's/\.//')
    
    # Disk metrics
    local disk_total=$(df -h / | awk 'NR==2 {print $2}')
    local disk_used=$(df -h / | awk 'NR==2 {print $3}')
    local disk_free=$(df -h / | awk 'NR==2 {print $4}')
    local disk_percent=$(df -h / | awk 'NR==2 {print $5}' | sed 's/%//')
    
    # Network metrics
    local network_in=$(netstat -ib | grep -E "en0|en1" | awk '{sum += $7} END {print sum}')
    local network_out=$(netstat -ib | grep -E "en0|en1" | awk '{sum += $10} END {print sum}')
    
    # Store metrics
    TELEMETRY_DATA["timestamp"]="$timestamp"
    TELEMETRY_DATA["cpu_usage"]="$cpu_usage"
    TELEMETRY_DATA["cpu_user"]="$cpu_user"
    TELEMETRY_DATA["cpu_sys"]="$cpu_sys"
    TELEMETRY_DATA["cpu_idle"]="$cpu_idle"
    TELEMETRY_DATA["memory_total"]="$memory_total"
    TELEMETRY_DATA["memory_used"]="$memory_used"
    TELEMETRY_DATA["memory_free"]="$memory_free"
    TELEMETRY_DATA["memory_wired"]="$memory_wired"
    TELEMETRY_DATA["disk_total"]="$disk_total"
    TELEMETRY_DATA["disk_used"]="$disk_used"
    TELEMETRY_DATA["disk_free"]="$disk_free"
    TELEMETRY_DATA["disk_percent"]="$disk_percent"
    TELEMETRY_DATA["network_in"]="$network_in"
    TELEMETRY_DATA["network_out"]="$network_out"
    
    if [ "$VERBOSE" = true ]; then
        log "System metrics collected: CPU $cpu_usage%, Memory $memory_used pages, Disk $disk_percent%"
    fi
}

# Function to collect ColibriDB metrics
collect_colibridb_metrics() {
    local timestamp=$(date +%s)
    
    # Try to get metrics from running server
    local server_metrics=""
    if curl -s http://localhost:8080/metrics >/dev/null 2>&1; then
        server_metrics=$(curl -s http://localhost:8080/metrics)
    fi
    
    # Buffer pool metrics
    local buffer_hits=0
    local buffer_misses=0
    local buffer_pages=0
    local buffer_capacity=0
    
    if [ -n "$server_metrics" ]; then
        buffer_hits=$(echo "$server_metrics" | grep "colibridb_buffer_hits" | awk '{print $2}' || echo "0")
        buffer_misses=$(echo "$server_metrics" | grep "colibridb_buffer_misses" | awk '{print $2}' || echo "0")
        buffer_pages=$(echo "$server_metrics" | grep "colibridb_buffer_pages" | awk '{print $2}' || echo "0")
        buffer_capacity=$(echo "$server_metrics" | grep "colibridb_buffer_capacity" | awk '{print $2}' || echo "0")
    fi
    
    # Query metrics
    local queries_total=0
    local queries_per_second=0
    local avg_query_time=0
    
    if [ -n "$server_metrics" ]; then
        queries_total=$(echo "$server_metrics" | grep "colibridb_queries_total" | awk '{print $2}' || echo "0")
        queries_per_second=$(echo "$server_metrics" | grep "colibridb_queries_per_second" | awk '{print $2}' || echo "0")
        avg_query_time=$(echo "$server_metrics" | grep "colibridb_avg_query_time" | awk '{print $2}' || echo "0")
    fi
    
    # Transaction metrics
    local transactions_total=0
    local active_transactions=0
    local committed_transactions=0
    local aborted_transactions=0
    
    if [ -n "$server_metrics" ]; then
        transactions_total=$(echo "$server_metrics" | grep "colibridb_transactions_total" | awk '{print $2}' || echo "0")
        active_transactions=$(echo "$server_metrics" | grep "colibridb_active_transactions" | awk '{print $2}' || echo "0")
        committed_transactions=$(echo "$server_metrics" | grep "colibridb_committed_transactions" | awk '{print $2}' || echo "0")
        aborted_transactions=$(echo "$server_metrics" | grep "colibridb_aborted_transactions" | awk '{print $2}' || echo "0")
    fi
    
    # Index metrics
    local index_hits=0
    local index_misses=0
    local index_scans=0
    
    if [ -n "$server_metrics" ]; then
        index_hits=$(echo "$server_metrics" | grep "colibridb_index_hits" | awk '{print $2}' || echo "0")
        index_misses=$(echo "$server_metrics" | grep "colibridb_index_misses" | awk '{print $2}' || echo "0")
        index_scans=$(echo "$server_metrics" | grep "colibridb_index_scans" | awk '{print $2}' || echo "0")
    fi
    
    # Store metrics
    METRICS_DATA["timestamp"]="$timestamp"
    METRICS_DATA["buffer_hits"]="$buffer_hits"
    METRICS_DATA["buffer_misses"]="$buffer_misses"
    METRICS_DATA["buffer_pages"]="$buffer_pages"
    METRICS_DATA["buffer_capacity"]="$buffer_capacity"
    METRICS_DATA["queries_total"]="$queries_total"
    METRICS_DATA["queries_per_second"]="$queries_per_second"
    METRICS_DATA["avg_query_time"]="$avg_query_time"
    METRICS_DATA["transactions_total"]="$transactions_total"
    METRICS_DATA["active_transactions"]="$active_transactions"
    METRICS_DATA["committed_transactions"]="$committed_transactions"
    METRICS_DATA["aborted_transactions"]="$aborted_transactions"
    METRICS_DATA["index_hits"]="$index_hits"
    METRICS_DATA["index_misses"]="$index_misses"
    METRICS_DATA["index_scans"]="$index_scans"
    
    if [ "$VERBOSE" = true ]; then
        log "ColibriDB metrics collected: Queries $queries_per_second/s, Buffer hit ratio $((buffer_hits * 100 / (buffer_hits + buffer_misses)))%"
    fi
}

# Function to collect profiling data
collect_profiling_data() {
    local timestamp=$(date +%s)
    
    # Process information
    local pid=$(pgrep -f "colibri-server" || echo "")
    if [ -n "$pid" ]; then
        # Memory usage
        local memory_usage=$(ps -o rss= -p "$pid" 2>/dev/null || echo "0")
        local memory_percent=$(ps -o %mem= -p "$pid" 2>/dev/null || echo "0")
        local cpu_percent=$(ps -o %cpu= -p "$pid" 2>/dev/null || echo "0")
        
        # File descriptors
        local fd_count=$(lsof -p "$pid" 2>/dev/null | wc -l || echo "0")
        
        # Thread count
        local thread_count=$(ps -M -p "$pid" 2>/dev/null | wc -l || echo "0")
        
        # Store profiling data
        PROFILING_DATA["timestamp"]="$timestamp"
        PROFILING_DATA["pid"]="$pid"
        PROFILING_DATA["memory_usage"]="$memory_usage"
        PROFILING_DATA["memory_percent"]="$memory_percent"
        PROFILING_DATA["cpu_percent"]="$cpu_percent"
        PROFILING_DATA["fd_count"]="$fd_count"
        PROFILING_DATA["thread_count"]="$thread_count"
        
        if [ "$VERBOSE" = true ]; then
            log "Profiling data collected: PID $pid, Memory ${memory_usage}KB, CPU ${cpu_percent}%"
        fi
    else
        warning "ColibriDB server not running, skipping profiling data"
    fi
}

# Function to collect log data
collect_log_data() {
    local timestamp=$(date +%s)
    
    # System logs
    local system_logs=""
    if [ -f "/var/log/system.log" ]; then
        system_logs=$(tail -n 100 /var/log/system.log | grep -i colibridb || echo "")
    fi
    
    # Application logs
    local app_logs=""
    if [ -f "$LOGS_DIR/server/server.log" ]; then
        app_logs=$(tail -n 100 "$LOGS_DIR/server/server.log" || echo "")
    fi
    
    # Error logs
    local error_logs=""
    if [ -f "$LOGS_DIR/server/error.log" ]; then
        error_logs=$(tail -n 100 "$LOGS_DIR/server/error.log" || echo "")
    fi
    
    # Store log data
    echo "$system_logs" > "$OUTPUT_DIR/system_logs_${timestamp}.log"
    echo "$app_logs" > "$OUTPUT_DIR/app_logs_${timestamp}.log"
    echo "$error_logs" > "$OUTPUT_DIR/error_logs_${timestamp}.log"
    
    if [ "$VERBOSE" = true ]; then
        log "Log data collected: System $(echo "$system_logs" | wc -l) lines, App $(echo "$app_logs" | wc -l) lines, Error $(echo "$error_logs" | wc -l) lines"
    fi
}

# Function to export telemetry data
export_telemetry_data() {
    local timestamp=$(date +%s)
    local export_file="$OUTPUT_DIR/telemetry_${timestamp}.${FORMAT}"
    
    case $FORMAT in
        json)
            # Generate JSON export
            cat > "$export_file" << EOF
{
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "collection_duration": $DURATION,
  "collection_interval": $INTERVAL,
  "system_metrics": {
EOF
            
            local first=true
            for key in "${!TELEMETRY_DATA[@]}"; do
                if [ "$first" = true ]; then
                    first=false
                else
                    echo "," >> "$export_file"
                fi
                echo "    \"$key\": \"${TELEMETRY_DATA[$key]}\"" >> "$export_file"
            done
            
            cat >> "$export_file" << EOF
  },
  "colibridb_metrics": {
EOF
            
            first=true
            for key in "${!METRICS_DATA[@]}"; do
                if [ "$first" = true ]; then
                    first=false
                else
                    echo "," >> "$export_file"
                fi
                echo "    \"$key\": \"${METRICS_DATA[$key]}\"" >> "$export_file"
            done
            
            cat >> "$export_file" << EOF
  },
  "profiling_data": {
EOF
            
            first=true
            for key in "${!PROFILING_DATA[@]}"; do
                if [ "$first" = true ]; then
                    first=false
                else
                    echo "," >> "$export_file"
                fi
                echo "    \"$key\": \"${PROFILING_DATA[$key]}\"" >> "$export_file"
            done
            
            cat >> "$export_file" << EOF
  }
}
EOF
            ;;
        csv)
            # Generate CSV export
            echo "timestamp,metric_type,metric_name,value" > "$export_file"
            
            for key in "${!TELEMETRY_DATA[@]}"; do
                echo "$timestamp,system,$key,${TELEMETRY_DATA[$key]}" >> "$export_file"
            done
            
            for key in "${!METRICS_DATA[@]}"; do
                echo "$timestamp,colibridb,$key,${METRICS_DATA[$key]}" >> "$export_file"
            done
            
            for key in "${!PROFILING_DATA[@]}"; do
                echo "$timestamp,profiling,$key,${PROFILING_DATA[$key]}" >> "$export_file"
            done
            ;;
        prometheus)
            # Generate Prometheus metrics
            cat > "$export_file" << EOF
# HELP colibridb_system_cpu_usage CPU usage percentage
# TYPE colibridb_system_cpu_usage gauge
colibridb_system_cpu_usage ${TELEMETRY_DATA[cpu_usage]}

# HELP colibridb_system_memory_used Memory used in pages
# TYPE colibridb_system_memory_used gauge
colibridb_system_memory_used ${TELEMETRY_DATA[memory_used]}

# HELP colibridb_buffer_hits Buffer pool hits
# TYPE colibridb_buffer_hits counter
colibridb_buffer_hits ${METRICS_DATA[buffer_hits]}

# HELP colibridb_buffer_misses Buffer pool misses
# TYPE colibridb_buffer_misses counter
colibridb_buffer_misses ${METRICS_DATA[buffer_misses]}

# HELP colibridb_queries_per_second Queries per second
# TYPE colibridb_queries_per_second gauge
colibridb_queries_per_second ${METRICS_DATA[queries_per_second]}

# HELP colibridb_active_transactions Active transactions
# TYPE colibridb_active_transactions gauge
colibridb_active_transactions ${METRICS_DATA[active_transactions]}
EOF
            ;;
    esac
    
    success "Telemetry data exported to: $export_file"
}

# Main telemetry collection
main() {
    log "Starting ColibrìDB telemetry collection..."
    log "Output directory: $OUTPUT_DIR"
    log "Duration: $DURATION seconds"
    log "Interval: $INTERVAL seconds"
    log "Format: $FORMAT"
    log "Include logs: $INCLUDE_LOGS"
    log "Include metrics: $INCLUDE_METRICS"
    log "Include profiling: $INCLUDE_PROFILING"
    
    local start_time=$(date +%s)
    local end_time=$((start_time + DURATION))
    local iteration=0
    
    # Create output directory
    mkdir -p "$OUTPUT_DIR"
    
    # Main collection loop
    while [ $(date +%s) -lt $end_time ]; do
        iteration=$((iteration + 1))
        log "Collection iteration $iteration"
        
        # Collect system metrics
        collect_system_metrics
        
        # Collect ColibriDB metrics
        if [ "$INCLUDE_METRICS" = true ]; then
            collect_colibridb_metrics
        fi
        
        # Collect profiling data
        if [ "$INCLUDE_PROFILING" = true ]; then
            collect_profiling_data
        fi
        
        # Collect log data
        if [ "$INCLUDE_LOGS" = true ]; then
            collect_log_data
        fi
        
        # Export current data
        export_telemetry_data
        
        # Wait for next interval
        sleep $INTERVAL
    done
    
    local total_duration=$(($(date +%s) - start_time))
    
    # Final export
    log "Generating final telemetry report..."
    export_telemetry_data
    
    # Generate summary
    log "Telemetry collection completed in ${total_duration}s"
    log "Total iterations: $iteration"
    log "Data exported to: $OUTPUT_DIR"
    
    success "Telemetry collection completed successfully!"
}

# Run main function
main "$@"
