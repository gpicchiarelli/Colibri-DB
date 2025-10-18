#!/usr/bin/env bash
#
# Benchmark JSON Converter for ColibrìDB
# Converts raw benchmark output to structured JSON format
#
# Usage:
#   bash bench_json.sh <input_file> <output_file>
#
# Input format (raw benchmark output):
#   BenchmarkName: p50=123us, p95=456us, p99=789us, ops/sec=10000
#
# Output format (JSON):
#   {
#     "timestamp": "2025-10-18T12:00:00Z",
#     "operations": {
#       "Category": {
#         "operation": {
#           "p50": 123, "p95": 456, "p99": 789,
#           "unit": "us", "throughput": 10000
#         }
#       }
#     }
#   }

set -euo pipefail

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check arguments
if [ $# -ne 2 ]; then
    echo -e "${RED}Usage: $0 <input_file> <output_file>${NC}"
    echo ""
    echo "Example:"
    echo "  $0 benchmark-results.txt benchmark-results.json"
    exit 1
fi

INPUT_FILE="$1"
OUTPUT_FILE="$2"

# Check input file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo -e "${RED}Error: Input file not found: $INPUT_FILE${NC}"
    exit 1
fi

# Function to extract metric value
extract_metric() {
    local line="$1"
    local metric="$2"
    echo "$line" | grep -oE "${metric}=[0-9.]+" | cut -d'=' -f2 || echo "0"
}

# Function to extract unit
extract_unit() {
    local line="$1"
    # Look for common units: us, ms, ns, s
    if echo "$line" | grep -q "us"; then
        echo "us"
    elif echo "$line" | grep -q "ms"; then
        echo "ms"
    elif echo "$line" | grep -q "ns"; then
        echo "ns"
    elif echo "$line" | grep -q " s"; then
        echo "s"
    else
        echo "us"  # default
    fi
}

# Start JSON output
echo -e "${GREEN}Converting benchmark results to JSON...${NC}"

cat > "$OUTPUT_FILE" << 'HEADER'
{
  "timestamp": "TIMESTAMP_PLACEHOLDER",
  "version": "1.0",
  "platform": "PLATFORM_PLACEHOLDER",
  "operations": {
HEADER

# Replace timestamp
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
PLATFORM=$(uname -sm)
sed -i.bak "s/TIMESTAMP_PLACEHOLDER/$TIMESTAMP/" "$OUTPUT_FILE"
sed -i.bak "s/PLATFORM_PLACEHOLDER/$PLATFORM/" "$OUTPUT_FILE"
rm -f "${OUTPUT_FILE}.bak"

# Parse benchmark output
first_category=true
current_category=""

while IFS= read -r line; do
    # Skip empty lines and headers
    if [[ -z "$line" ]] || [[ "$line" =~ ^=+$ ]] || [[ "$line" =~ ^-+$ ]]; then
        continue
    fi
    
    # Detect category headers (e.g., "WAL Benchmarks:")
    if [[ "$line" =~ ^[A-Z][A-Za-z ]+:$ ]]; then
        new_category=$(echo "$line" | sed 's/:.*//' | sed 's/ Benchmarks//' | tr ' ' '_')
        
        # Close previous category if exists
        if [ -n "$current_category" ]; then
            echo "    }," >> "$OUTPUT_FILE"
        fi
        
        current_category="$new_category"
        
        # Start new category
        if [ "$first_category" = true ]; then
            echo "    \"$current_category\": {" >> "$OUTPUT_FILE"
            first_category=false
        else
            echo "    \"$current_category\": {" >> "$OUTPUT_FILE"
        fi
        
        first_operation=true
        continue
    fi
    
    # Parse operation line (e.g., "append_single: p50=100us, p95=250us, p99=500us")
    if [[ "$line" =~ ^[[:space:]]*[a-z_]+: ]] && [ -n "$current_category" ]; then
        operation=$(echo "$line" | awk -F: '{print $1}' | xargs)
        
        # Extract metrics
        p50=$(extract_metric "$line" "p50")
        p95=$(extract_metric "$line" "p95")
        p99=$(extract_metric "$line" "p99")
        throughput=$(extract_metric "$line" "ops/sec")
        unit=$(extract_unit "$line")
        
        # Remove unit suffixes from values
        p50=$(echo "$p50" | sed 's/[a-z]*$//')
        p95=$(echo "$p95" | sed 's/[a-z]*$//')
        p99=$(echo "$p99" | sed 's/[a-z]*$//')
        
        # Add comma before operation if not first
        if [ "$first_operation" = false ]; then
            echo "," >> "$OUTPUT_FILE"
        fi
        first_operation=false
        
        # Write operation JSON (without trailing newline for comma handling)
        cat >> "$OUTPUT_FILE" << OPERATION
      "$operation": {
        "p50": $p50,
        "p95": $p95,
        "p99": $p99,
        "unit": "$unit",
        "throughput": $throughput
      }
OPERATION
    fi
done < "$INPUT_FILE"

# Close last category
if [ -n "$current_category" ]; then
    echo "" >> "$OUTPUT_FILE"
    echo "    }" >> "$OUTPUT_FILE"
fi

# Close JSON
cat >> "$OUTPUT_FILE" << 'FOOTER'
  },
  "metadata": {
    "total_benchmarks": "N/A",
    "duration_seconds": "N/A",
    "runner": "ColibrìDB Benchmark Suite"
  }
}
FOOTER

# Validate JSON
if command -v python3 &> /dev/null; then
    if python3 -m json.tool "$OUTPUT_FILE" > /dev/null 2>&1; then
        echo -e "${GREEN}✓ Valid JSON created: $OUTPUT_FILE${NC}"
    else
        echo -e "${RED}✗ Invalid JSON generated${NC}"
        exit 1
    fi
else
    echo -e "${YELLOW}⚠ Python3 not found, skipping JSON validation${NC}"
fi

# Print summary
echo ""
echo "Benchmark conversion complete!"
echo "  Input:  $INPUT_FILE"
echo "  Output: $OUTPUT_FILE"
echo ""

# Show sample of output
echo "Sample output:"
head -n 20 "$OUTPUT_FILE"
echo "..."

exit 0

