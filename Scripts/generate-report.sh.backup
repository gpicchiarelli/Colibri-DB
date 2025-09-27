#!/bin/bash

# ColibrìDB Report Generator Script
# Comprehensive reporting and analysis system

set -e

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
REPORTS_DIR="$DEV_DIR/reports"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Report configuration
CYCLE_ID=""
OUTPUT_DIR=""
FORMAT="html"
INCLUDE_CHARTS=true
INCLUDE_METRICS=true
INCLUDE_LOGS=true
INCLUDE_BENCHMARKS=true
VERBOSE=false

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
        --cycle)
            CYCLE_ID="$2"
            shift 2
            ;;
        --output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --format)
            FORMAT="$2"
            shift 2
            ;;
        --no-charts)
            INCLUDE_CHARTS=false
            shift
            ;;
        --no-metrics)
            INCLUDE_METRICS=false
            shift
            ;;
        --no-logs)
            INCLUDE_LOGS=false
            shift
            ;;
        --no-benchmarks)
            INCLUDE_BENCHMARKS=false
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --cycle ID         Test cycle ID"
            echo "  --output DIR       Output directory for report"
            echo "  --format FORMAT    Report format (html|pdf|json|markdown)"
            echo "  --no-charts        Skip chart generation"
            echo "  --no-metrics       Skip metrics analysis"
            echo "  --no-logs          Skip log analysis"
            echo "  --no-benchmarks    Skip benchmark analysis"
            echo "  --verbose          Verbose output"
            echo "  --help             Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Default values
if [ -z "$CYCLE_ID" ]; then
    CYCLE_ID="$(date +%Y%m%d_%H%M%S)"
fi

if [ -z "$OUTPUT_DIR" ]; then
    OUTPUT_DIR="$REPORTS_DIR/test-results/cycle-$CYCLE_ID"
fi

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Report data
# Note: Using temporary files instead of associative arrays for macOS compatibility REPORT_DATA
# Note: Using temporary files instead of associative arrays for macOS compatibility TEST_RESULTS
# Note: Using temporary files instead of associative arrays for macOS compatibility BENCHMARK_RESULTS
# Note: Using temporary files instead of associative arrays for macOS compatibility TELEMETRY_DATA
# Note: Using temporary files instead of associative arrays for macOS compatibility SYSTEM_METRICS

# Function to load test results
load_test_results() {
    log "Loading test results..."
    
    local test_file="$REPORTS_DIR/test-results/test-results.csv"
    if [ -f "$test_file" ]; then
        # Parse CSV and extract data
        local total_tests=0
        local passed_tests=0
        local failed_tests=0
        local total_duration=0
        
        while IFS=',' read -r timestamp test_name test_type exit_code duration; do
            if [ "$test_name" != "test_name" ]; then  # Skip header
                total_tests=$((total_tests + 1))
                total_duration=$((total_duration + duration))
                
                if [ "$exit_code" = "0" ]; then
                    passed_tests=$((passed_tests + 1))
                else
                    failed_tests=$((failed_tests + 1))
                fi
                
                TEST_RESULTS["$test_name"]="$exit_code,$duration"
            fi
        done < "$test_file"
        
        REPORT_DATA["total_tests"]="$total_tests"
        REPORT_DATA["passed_tests"]="$passed_tests"
        REPORT_DATA["failed_tests"]="$failed_tests"
        REPORT_DATA["total_duration"]="$total_duration"
        
        if [ $total_tests -gt 0 ]; then
            local success_rate=$((passed_tests * 100 / total_tests))
            REPORT_DATA["success_rate"]="$success_rate"
        else
            REPORT_DATA["success_rate"]="0"
        fi
        
        success "Test results loaded: $total_tests tests, $passed_tests passed, $failed_tests failed"
    else
        warning "Test results file not found: $test_file"
    fi
}

# Function to load benchmark results
load_benchmark_results() {
    if [ "$INCLUDE_BENCHMARKS" = false ]; then
        return
    fi
    
    log "Loading benchmark results..."
    
    local benchmark_file="$REPORTS_DIR/benchmarks/benchmark-results.csv"
    if [ -f "$benchmark_file" ]; then
        local total_benchmarks=0
        local total_throughput=0
        local total_latency=0
        
        while IFS=',' read -r timestamp benchmark_name benchmark_type exit_code duration throughput latency memory; do
            if [ "$benchmark_name" != "benchmark_name" ]; then  # Skip header
                total_benchmarks=$((total_benchmarks + 1))
                total_throughput=$(echo "$total_throughput + $throughput" | bc -l 2>/dev/null || echo "$total_throughput")
                total_latency=$(echo "$total_latency + $latency" | bc -l 2>/dev/null || echo "$total_latency")
                
                BENCHMARK_RESULTS["$benchmark_name"]="$throughput,$latency,$memory"
            fi
        done < "$benchmark_file"
        
        REPORT_DATA["total_benchmarks"]="$total_benchmarks"
        REPORT_DATA["avg_throughput"]=$(echo "scale=2; $total_throughput / $total_benchmarks" | bc -l 2>/dev/null || echo "0")
        REPORT_DATA["avg_latency"]=$(echo "scale=2; $total_latency / $total_benchmarks" | bc -l 2>/dev/null || echo "0")
        
        success "Benchmark results loaded: $total_benchmarks benchmarks"
    else
        warning "Benchmark results file not found: $benchmark_file"
    fi
}

# Function to load telemetry data
load_telemetry_data() {
    if [ "$INCLUDE_METRICS" = false ]; then
        return
    fi
    
    log "Loading telemetry data..."
    
    # Find latest telemetry file
    local telemetry_dir="$REPORTS_DIR/telemetry"
    local latest_file=""
    
    if [ -d "$telemetry_dir" ]; then
        latest_file=$(find "$telemetry_dir" -name "telemetry_*.json" -type f -printf '%T@ %p\n' | sort -n | tail -1 | cut -d' ' -f2-)
    fi
    
    if [ -n "$latest_file" ] && [ -f "$latest_file" ]; then
        # Parse JSON and extract metrics
        local cpu_usage=$(jq -r '.system_metrics.cpu_usage // "0"' "$latest_file" 2>/dev/null || echo "0")
        local memory_used=$(jq -r '.system_metrics.memory_used // "0"' "$latest_file" 2>/dev/null || echo "0")
        local queries_per_second=$(jq -r '.colibridb_metrics.queries_per_second // "0"' "$latest_file" 2>/dev/null || echo "0")
        local buffer_hits=$(jq -r '.colibridb_metrics.buffer_hits // "0"' "$latest_file" 2>/dev/null || echo "0")
        local buffer_misses=$(jq -r '.colibridb_metrics.buffer_misses // "0"' "$latest_file" 2>/dev/null || echo "0")
        
        TELEMETRY_DATA["cpu_usage"]="$cpu_usage"
        TELEMETRY_DATA["memory_used"]="$memory_used"
        TELEMETRY_DATA["queries_per_second"]="$queries_per_second"
        TELEMETRY_DATA["buffer_hits"]="$buffer_hits"
        TELEMETRY_DATA["buffer_misses"]="$buffer_misses"
        
        # Calculate buffer hit ratio
        local total_buffer_ops=$((buffer_hits + buffer_misses))
        if [ $total_buffer_ops -gt 0 ]; then
            local hit_ratio=$(echo "scale=2; $buffer_hits * 100 / $total_buffer_ops" | bc -l 2>/dev/null || echo "0")
            TELEMETRY_DATA["buffer_hit_ratio"]="$hit_ratio"
        else
            TELEMETRY_DATA["buffer_hit_ratio"]="0"
        fi
        
        success "Telemetry data loaded: CPU ${cpu_usage}%, Memory ${memory_used} pages, Queries ${queries_per_second}/s"
    else
        warning "Telemetry data file not found"
    fi
}

# Function to generate HTML report
generate_html_report() {
    log "Generating HTML report..."
    
    local report_file="$OUTPUT_DIR/report.html"
    
    cat > "$report_file" << EOF
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>ColibrìDB Test Report - Cycle $CYCLE_ID</title>
    <style>
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            line-height: 1.6;
            margin: 0;
            padding: 20px;
            background-color: #f5f5f5;
        }
        .container {
            max-width: 1200px;
            margin: 0 auto;
            background: white;
            padding: 30px;
            border-radius: 8px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }
        .header {
            text-align: center;
            border-bottom: 2px solid #007AFF;
            padding-bottom: 20px;
            margin-bottom: 30px;
        }
        .header h1 {
            color: #007AFF;
            margin: 0;
            font-size: 2.5em;
        }
        .header p {
            color: #666;
            margin: 10px 0 0 0;
        }
        .summary {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            margin-bottom: 30px;
        }
        .summary-card {
            background: #f8f9fa;
            padding: 20px;
            border-radius: 6px;
            text-align: center;
            border-left: 4px solid #007AFF;
        }
        .summary-card h3 {
            margin: 0 0 10px 0;
            color: #333;
        }
        .summary-card .value {
            font-size: 2em;
            font-weight: bold;
            color: #007AFF;
        }
        .summary-card .label {
            color: #666;
            font-size: 0.9em;
        }
        .section {
            margin-bottom: 30px;
        }
        .section h2 {
            color: #333;
            border-bottom: 1px solid #ddd;
            padding-bottom: 10px;
        }
        .test-results {
            overflow-x: auto;
        }
        table {
            width: 100%;
            border-collapse: collapse;
            margin-top: 15px;
        }
        th, td {
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid #ddd;
        }
        th {
            background-color: #f8f9fa;
            font-weight: 600;
        }
        .status-pass {
            color: #28a745;
            font-weight: bold;
        }
        .status-fail {
            color: #dc3545;
            font-weight: bold;
        }
        .metrics-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 20px;
        }
        .metric-card {
            background: #f8f9fa;
            padding: 20px;
            border-radius: 6px;
        }
        .metric-card h4 {
            margin: 0 0 15px 0;
            color: #333;
        }
        .metric-value {
            font-size: 1.5em;
            font-weight: bold;
            color: #007AFF;
        }
        .footer {
            text-align: center;
            margin-top: 40px;
            padding-top: 20px;
            border-top: 1px solid #ddd;
            color: #666;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>ColibrìDB Test Report</h1>
            <p>Cycle: $CYCLE_ID | Generated: $(date)</p>
        </div>
        
        <div class="summary">
            <div class="summary-card">
                <h3>Total Tests</h3>
                <div class="value">${REPORT_DATA[total_tests]}</div>
                <div class="label">Tests Executed</div>
            </div>
            <div class="summary-card">
                <h3>Success Rate</h3>
                <div class="value">${REPORT_DATA[success_rate]}%</div>
                <div class="label">Tests Passed</div>
            </div>
            <div class="summary-card">
                <h3>Duration</h3>
                <div class="value">${REPORT_DATA[total_duration]}s</div>
                <div class="label">Total Time</div>
            </div>
            <div class="summary-card">
                <h3>Benchmarks</h3>
                <div class="value">${REPORT_DATA[total_benchmarks]}</div>
                <div class="label">Performance Tests</div>
            </div>
        </div>
        
        <div class="section">
            <h2>Test Results</h2>
            <div class="test-results">
                <table>
                    <thead>
                        <tr>
                            <th>Test Name</th>
                            <th>Status</th>
                            <th>Duration (s)</th>
                        </tr>
                    </thead>
                    <tbody>
EOF

    # Add test results to table
    for test_name in "${!TEST_RESULTS[@]}"; do
        local result_data="${TEST_RESULTS[$test_name]}"
        local exit_code=$(echo "$result_data" | cut -d',' -f1)
        local duration=$(echo "$result_data" | cut -d',' -f2)
        
        local status_class="status-fail"
        local status_text="FAIL"
        if [ "$exit_code" = "0" ]; then
            status_class="status-pass"
            status_text="PASS"
        fi
        
        cat >> "$report_file" << EOF
                        <tr>
                            <td>$test_name</td>
                            <td class="$status_class">$status_text</td>
                            <td>$duration</td>
                        </tr>
EOF
    done

    cat >> "$report_file" << EOF
                    </tbody>
                </table>
            </div>
        </div>
        
        <div class="section">
            <h2>Performance Metrics</h2>
            <div class="metrics-grid">
                <div class="metric-card">
                    <h4>CPU Usage</h4>
                    <div class="metric-value">${TELEMETRY_DATA[cpu_usage]}%</div>
                </div>
                <div class="metric-card">
                    <h4>Memory Usage</h4>
                    <div class="metric-value">${TELEMETRY_DATA[memory_used]} pages</div>
                </div>
                <div class="metric-card">
                    <h4>Queries per Second</h4>
                    <div class="metric-value">${TELEMETRY_DATA[queries_per_second]}</div>
                </div>
                <div class="metric-card">
                    <h4>Buffer Hit Ratio</h4>
                    <div class="metric-value">${TELEMETRY_DATA[buffer_hit_ratio]}%</div>
                </div>
                <div class="metric-card">
                    <h4>Average Throughput</h4>
                    <div class="metric-value">${REPORT_DATA[avg_throughput]} ops/s</div>
                </div>
                <div class="metric-card">
                    <h4>Average Latency</h4>
                    <div class="metric-value">${REPORT_DATA[avg_latency]} ms</div>
                </div>
            </div>
        </div>
        
        <div class="footer">
            <p>Generated by ColibrìDB Development Environment</p>
        </div>
    </div>
</body>
</html>
EOF

    success "HTML report generated: $report_file"
}

# Function to generate JSON report
generate_json_report() {
    log "Generating JSON report..."
    
    local report_file="$OUTPUT_DIR/report.json"
    
    cat > "$report_file" << EOF
{
  "cycle_id": "$CYCLE_ID",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "summary": {
    "total_tests": ${REPORT_DATA[total_tests]},
    "passed_tests": ${REPORT_DATA[passed_tests]},
    "failed_tests": ${REPORT_DATA[failed_tests]},
    "success_rate": ${REPORT_DATA[success_rate]},
    "total_duration": ${REPORT_DATA[total_duration]},
    "total_benchmarks": ${REPORT_DATA[total_benchmarks]},
    "avg_throughput": ${REPORT_DATA[avg_throughput]},
    "avg_latency": ${REPORT_DATA[avg_latency]}
  },
  "test_results": {
EOF

    local first=true
    for test_name in "${!TEST_RESULTS[@]}"; do
        local result_data="${TEST_RESULTS[$test_name]}"
        local exit_code=$(echo "$result_data" | cut -d',' -f1)
        local duration=$(echo "$result_data" | cut -d',' -f2)
        
        if [ "$first" = true ]; then
            first=false
        else
            echo "," >> "$report_file"
        fi
        
        cat >> "$report_file" << EOF
    "$test_name": {
      "exit_code": $exit_code,
      "duration": $duration,
      "status": "$([ "$exit_code" = "0" ] && echo "pass" || echo "fail")"
    }
EOF
    done

    cat >> "$report_file" << EOF
  },
  "telemetry": {
    "cpu_usage": "${TELEMETRY_DATA[cpu_usage]}",
    "memory_used": "${TELEMETRY_DATA[memory_used]}",
    "queries_per_second": "${TELEMETRY_DATA[queries_per_second]}",
    "buffer_hits": "${TELEMETRY_DATA[buffer_hits]}",
    "buffer_misses": "${TELEMETRY_DATA[buffer_misses]}",
    "buffer_hit_ratio": "${TELEMETRY_DATA[buffer_hit_ratio]}"
  },
  "benchmark_results": {
EOF

    first=true
    for benchmark_name in "${!BENCHMARK_RESULTS[@]}"; do
        local result_data="${BENCHMARK_RESULTS[$benchmark_name]}"
        local throughput=$(echo "$result_data" | cut -d',' -f1)
        local latency=$(echo "$result_data" | cut -d',' -f2)
        local memory=$(echo "$result_data" | cut -d',' -f3)
        
        if [ "$first" = true ]; then
            first=false
        else
            echo "," >> "$report_file"
        fi
        
        cat >> "$report_file" << EOF
    "$benchmark_name": {
      "throughput": $throughput,
      "latency": $latency,
      "memory": $memory
    }
EOF
    done

    cat >> "$report_file" << EOF
  }
}
EOF

    success "JSON report generated: $report_file"
}

# Function to generate Markdown report
generate_markdown_report() {
    log "Generating Markdown report..."
    
    local report_file="$OUTPUT_DIR/report.md"
    
    cat > "$report_file" << EOF
# ColibrìDB Test Report

**Cycle:** $CYCLE_ID  
**Generated:** $(date)  
**Format:** Markdown

## Summary

| Metric | Value |
|--------|-------|
| Total Tests | ${REPORT_DATA[total_tests]} |
| Passed Tests | ${REPORT_DATA[passed_tests]} |
| Failed Tests | ${REPORT_DATA[failed_tests]} |
| Success Rate | ${REPORT_DATA[success_rate]}% |
| Total Duration | ${REPORT_DATA[total_duration]}s |
| Total Benchmarks | ${REPORT_DATA[total_benchmarks]} |
| Average Throughput | ${REPORT_DATA[avg_throughput]} ops/s |
| Average Latency | ${REPORT_DATA[avg_latency]} ms |

## Test Results

| Test Name | Status | Duration (s) |
|-----------|--------|--------------|
EOF

    # Add test results to table
    for test_name in "${!TEST_RESULTS[@]}"; do
        local result_data="${TEST_RESULTS[$test_name]}"
        local exit_code=$(echo "$result_data" | cut -d',' -f1)
        local duration=$(echo "$result_data" | cut -d',' -f2)
        
        local status_text="❌ FAIL"
        if [ "$exit_code" = "0" ]; then
            status_text="✅ PASS"
        fi
        
        cat >> "$report_file" << EOF
| $test_name | $status_text | $duration |
EOF
    done

    cat >> "$report_file" << EOF

## Performance Metrics

| Metric | Value |
|--------|-------|
| CPU Usage | ${TELEMETRY_DATA[cpu_usage]}% |
| Memory Usage | ${TELEMETRY_DATA[memory_used]} pages |
| Queries per Second | ${TELEMETRY_DATA[queries_per_second]} |
| Buffer Hit Ratio | ${TELEMETRY_DATA[buffer_hit_ratio]}% |

## Benchmark Results

| Benchmark | Throughput | Latency | Memory |
|-----------|------------|---------|--------|
EOF

    # Add benchmark results to table
    for benchmark_name in "${!BENCHMARK_RESULTS[@]}"; do
        local result_data="${BENCHMARK_RESULTS[$benchmark_name]}"
        local throughput=$(echo "$result_data" | cut -d',' -f1)
        local latency=$(echo "$result_data" | cut -d',' -f2)
        local memory=$(echo "$result_data" | cut -d',' -f3)
        
        cat >> "$report_file" << EOF
| $benchmark_name | $throughput | $latency | $memory |
EOF
    done

    cat >> "$report_file" << EOF

---
*Generated by ColibrìDB Development Environment*
EOF

    success "Markdown report generated: $report_file"
}

# Main report generation
main() {
    log "Starting ColibrìDB report generation..."
    log "Cycle ID: $CYCLE_ID"
    log "Output directory: $OUTPUT_DIR"
    log "Format: $FORMAT"
    log "Include charts: $INCLUDE_CHARTS"
    log "Include metrics: $INCLUDE_METRICS"
    log "Include logs: $INCLUDE_LOGS"
    log "Include benchmarks: $INCLUDE_BENCHMARKS"
    
    # Load data
    load_test_results
    load_benchmark_results
    load_telemetry_data
    
    # Generate report based on format
    case $FORMAT in
        html)
            generate_html_report
            ;;
        json)
            generate_json_report
            ;;
        markdown)
            generate_markdown_report
            ;;
        *)
            error "Unsupported format: $FORMAT"
            exit 1
            ;;
    esac
    
    success "Report generation completed successfully!"
    log "Report saved to: $OUTPUT_DIR"
}

# Run main function
main "$@"
