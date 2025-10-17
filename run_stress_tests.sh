#!/bin/bash
#
# Stress Test Suite Runner
# Esegue tutti gli stress test (600k ops ciascuno)
#

set -e

echo "🔥 Colibrì-DB Stress Test Suite"
echo "================================"
echo ""
echo "Ogni test esegue 600,000 operazioni"
echo "Tempo stimato: ~15-20 minuti"
echo ""

# Build benchmarks
echo "📦 Building benchmarks..."
swift build --product benchmarks > /dev/null 2>&1
echo "✅ Build complete"
echo ""

# Output directory
OUTPUT_DIR="stress_test_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUTPUT_DIR"
echo "📁 Results will be saved to: $OUTPUT_DIR"
echo ""

# Array of stress tests
TESTS=(
    "stress-heap-insert"
    "stress-btree-lookup"
    "stress-tx-commit"
    "stress-mixed-workload"
    "stress-index-ops"
    "stress-concurrent-ops"
    "stress-wal-append"
    "stress-scan-growing"
    "stress-multi-index"
    "stress-memory-pressure"
    "stress-range-queries"
)

FAILED=()
PASSED=()

for test in "${TESTS[@]}"; do
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "🧪 Running: $test"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    
    START_TIME=$(date +%s)
    
    if .build/debug/benchmarks "$test" --sysmetrics --json --out="$OUTPUT_DIR/$test.json" 2>&1 | tee "$OUTPUT_DIR/$test.log"; then
        END_TIME=$(date +%s)
        DURATION=$((END_TIME - START_TIME))
        echo ""
        echo "✅ $test completed in ${DURATION}s"
        echo ""
        PASSED+=("$test")
    else
        END_TIME=$(date +%s)
        DURATION=$((END_TIME - START_TIME))
        echo ""
        echo "❌ $test failed after ${DURATION}s"
        echo ""
        FAILED+=("$test")
    fi
done

# Summary
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 STRESS TEST SUMMARY"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "✅ Passed: ${#PASSED[@]}/${#TESTS[@]}"
for test in "${PASSED[@]}"; do
    echo "  ✓ $test"
done
echo ""

if [ ${#FAILED[@]} -gt 0 ]; then
    echo "❌ Failed: ${#FAILED[@]}/${#TESTS[@]}"
    for test in "${FAILED[@]}"; do
        echo "  ✗ $test"
    done
    echo ""
fi

echo "📁 Results saved to: $OUTPUT_DIR"
echo ""

# Generate summary report
SUMMARY_FILE="$OUTPUT_DIR/SUMMARY.md"
cat > "$SUMMARY_FILE" << EOF
# Stress Test Suite Results

**Date:** $(date)  
**Total Tests:** ${#TESTS[@]}  
**Passed:** ${#PASSED[@]}  
**Failed:** ${#FAILED[@]}

## Test Details

EOF

for test in "${TESTS[@]}"; do
    if [ -f "$OUTPUT_DIR/$test.json" ]; then
        echo "### $test" >> "$SUMMARY_FILE"
        echo "" >> "$SUMMARY_FILE"
        echo "\`\`\`json" >> "$SUMMARY_FILE"
        cat "$OUTPUT_DIR/$test.json" >> "$SUMMARY_FILE"
        echo "" >> "$SUMMARY_FILE"
        echo "\`\`\`" >> "$SUMMARY_FILE"
        echo "" >> "$SUMMARY_FILE"
    fi
done

echo "📄 Summary report: $SUMMARY_FILE"
echo ""
echo "🎉 Stress test suite complete!"

