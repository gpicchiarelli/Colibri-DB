#!/bin/bash

# Benchmark Results to JSON Converter
# Converts raw benchmark output to structured JSON format

set -e

if [ $# -lt 2 ]; then
    echo "Usage: $0 <input_file> <output_file>"
    echo "  input_file:  Raw benchmark output"
    echo "  output_file: JSON output file"
    exit 1
fi

INPUT_FILE="$1"
OUTPUT_FILE="$2"

if [ ! -f "$INPUT_FILE" ]; then
    echo "Error: Input file '$INPUT_FILE' not found"
    exit 1
fi

echo "Converting benchmark results from '$INPUT_FILE' to '$OUTPUT_FILE'..."

# Create temporary files
TEMP_DIR=$(mktemp -d)
TEMP_JSON="$TEMP_DIR/benchmarks.json"

# Initialize JSON structure
cat > "$TEMP_JSON" << 'EOF'
{
  "metadata": {
    "converter": "bench_json.sh",
    "version": "1.0.0",
    "timestamp": ""
  },
  "benchmarks": []
}
EOF

# Add timestamp
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
sed -i.bak "s/\"timestamp\": \"\"/\"timestamp\": \"$TIMESTAMP\"/" "$TEMP_JSON"
rm -f "$TEMP_JSON.bak"

# Parse benchmark results
# This is a simplified parser - in practice, you'd want more sophisticated parsing
# based on your actual benchmark output format

# Extract benchmark data using awk
awk '
BEGIN {
    print "[" > "'"$TEMP_DIR"'/benchmarks.json"
    first = 1
}

/^Benchmark:/ {
    if (!first) print "," >> "'"$TEMP_DIR"'/benchmarks.json"
    first = 0
    
    # Extract operation name
    operation = $2
    gsub(/[^a-zA-Z0-9_-]/, "_", operation)
    
    print "  {" >> "'"$TEMP_DIR"'/benchmarks.json"
    print "    \"operation\": \"" operation "\"," >> "'"$TEMP_DIR"'/benchmarks.json"
    print "    \"metrics\": {" >> "'"$TEMP_DIR"'/benchmarks.json"
}

/p50:/ {
    p50 = $2
    gsub(/[^0-9.]/, "", p50)
    print "      \"p50\": " p50 "," >> "'"$TEMP_DIR"'/benchmarks.json"
}

/p95:/ {
    p95 = $2
    gsub(/[^0-9.]/, "", p95)
    print "      \"p95\": " p95 "," >> "'"$TEMP_DIR"'/benchmarks.json"
}

/p99:/ {
    p99 = $2
    gsub(/[^0-9.]/, "", p99)
    print "      \"p99\": " p99 "," >> "'"$TEMP_DIR"'/benchmarks.json"
}

/unit:/ {
    unit = $2
    gsub(/[^a-zA-Z]/, "", unit)
    print "      \"unit\": \"" unit "\"," >> "'"$TEMP_DIR"'/benchmarks.json"
}

/throughput:/ {
    throughput = $2
    gsub(/[^0-9.]/, "", throughput)
    print "      \"throughput\": " throughput "," >> "'"$TEMP_DIR"'/benchmarks.json"
}

/description:/ {
    # Extract description (everything after "description:")
    description = substr($0, index($0, "description:") + 12)
    gsub(/^[ \t]+|[ \t]+$/, "", description)
    gsub(/"/, "\\\"", description)
    print "      \"description\": \"" description "\"" >> "'"$TEMP_DIR"'/benchmarks.json"
    print "    }," >> "'"$TEMP_DIR"'/benchmarks.json"
    print "    \"status\": \"completed\"" >> "'"$TEMP_DIR"'/benchmarks.json"
    print "  }" >> "'"$TEMP_DIR"'/benchmarks.json"
}

END {
    print "]" >> "'"$TEMP_DIR"'/benchmarks.json"
}
' "$INPUT_FILE"

# If no benchmarks were found, create a simple structure
if [ ! -s "$TEMP_DIR/benchmarks.json" ] || [ "$(wc -l < "$TEMP_DIR/benchmarks.json")" -lt 3 ]; then
    echo "No structured benchmarks found, creating fallback format..."
    
    # Create a simple fallback based on the input file
    cat > "$TEMP_JSON" << EOF
{
  "metadata": {
    "converter": "bench_json.sh",
    "version": "1.0.0",
    "timestamp": "$TIMESTAMP",
    "note": "Fallback conversion - raw output preserved"
  },
  "raw_output": $(cat "$INPUT_FILE" | jq -R -s .),
  "benchmarks": []
}
EOF
else
    # Merge with metadata
    jq --slurpfile benchmarks "$TEMP_DIR/benchmarks.json" '
        .benchmarks = $benchmarks[0]
    ' "$TEMP_JSON" > "$OUTPUT_FILE"
fi

# Clean up
rm -rf "$TEMP_DIR"

echo "✅ Benchmark results converted successfully"
echo "   Input:  $INPUT_FILE"
echo "   Output: $OUTPUT_FILE"

# Validate JSON
if jq empty "$OUTPUT_FILE" 2>/dev/null; then
    echo "✅ JSON validation passed"
else
    echo "❌ JSON validation failed"
    exit 1
fi