#!/usr/bin/env python3

"""
Performance Guard Script for ColibrìDB
Validates benchmark results against performance baselines
"""

import json
import sys
import argparse
from typing import Dict, Any, List, Optional
from dataclasses import dataclass

@dataclass
class PerformanceResult:
    operation: str
    p50: float
    p95: float
    p99: float
    unit: str
    description: str

@dataclass
class BaselineThresholds:
    p50: float
    p95: float
    p99: float

@dataclass
class ValidationResult:
    operation: str
    passed: bool
    violations: List[str]
    actual: PerformanceResult
    baseline: PerformanceResult
    thresholds: BaselineThresholds

class PerformanceGuard:
    def __init__(self, baseline_file: str):
        with open(baseline_file, 'r') as f:
            self.baseline_data = json.load(f)
        
        self.tolerance = self.baseline_data.get('tolerance', {})
        self.operations = self.baseline_data.get('operations', {})
        self.system = self.baseline_data.get('system', {})
    
    def load_benchmark_results(self, results_file: str) -> Dict[str, Any]:
        """Load benchmark results from JSON file"""
        with open(results_file, 'r') as f:
            return json.load(f)
    
    def parse_benchmark_results(self, results: Dict[str, Any]) -> List[PerformanceResult]:
        """Parse benchmark results into standardized format"""
        parsed_results = []
        
        # Handle different benchmark result formats
        if 'benchmarks' in results:
            # Structured format
            for benchmark in results['benchmarks']:
                if 'operation' in benchmark and 'metrics' in benchmark:
                    metrics = benchmark['metrics']
                    parsed_results.append(PerformanceResult(
                        operation=benchmark['operation'],
                        p50=metrics.get('p50', 0),
                        p95=metrics.get('p95', 0),
                        p99=metrics.get('p99', 0),
                        unit=metrics.get('unit', 'us'),
                        description=benchmark.get('description', '')
                    ))
        else:
            # Simple format - try to extract from raw text
            for key, value in results.items():
                if isinstance(value, dict) and 'p50' in value:
                    parsed_results.append(PerformanceResult(
                        operation=key,
                        p50=value.get('p50', 0),
                        p95=value.get('p95', 0),
                        p99=value.get('p99', 0),
                        unit=value.get('unit', 'us'),
                        description=value.get('description', '')
                    ))
        
        return parsed_results
    
    def find_baseline(self, operation: str) -> Optional[Dict[str, Any]]:
        """Find baseline for a specific operation"""
        # Search in operations
        for category, ops in self.operations.items():
            if operation in ops:
                return ops[operation]
        
        # Search in system
        if operation in self.system:
            return self.system[operation]
        
        return None
    
    def validate_operation(self, result: PerformanceResult) -> ValidationResult:
        """Validate a single operation against its baseline"""
        baseline = self.find_baseline(result.operation)
        
        if not baseline:
            return ValidationResult(
                operation=result.operation,
                passed=True,  # Skip unknown operations
                violations=[],
                actual=result,
                baseline=result,
                thresholds=BaselineThresholds(0, 0, 0)
            )
        
        # Calculate thresholds
        p50_threshold = baseline['p50'] * (1 + self.tolerance.get('p50', 0.05))
        p95_threshold = baseline['p95'] * (1 + self.tolerance.get('p95', 0.10))
        p99_threshold = baseline['p99'] * (1 + self.tolerance.get('p99', 0.15))
        
        thresholds = BaselineThresholds(p50_threshold, p95_threshold, p99_threshold)
        
        # Check violations
        violations = []
        if result.p50 > p50_threshold:
            violations.append(f"p50: {result.p50:.1f} > {p50_threshold:.1f} (baseline: {baseline['p50']:.1f})")
        if result.p95 > p95_threshold:
            violations.append(f"p95: {result.p95:.1f} > {p95_threshold:.1f} (baseline: {baseline['p95']:.1f})")
        if result.p99 > p99_threshold:
            violations.append(f"p99: {result.p99:.1f} > {p99_threshold:.1f} (baseline: {baseline['p99']:.1f})")
        
        baseline_result = PerformanceResult(
            operation=result.operation,
            p50=baseline['p50'],
            p95=baseline['p95'],
            p99=baseline['p99'],
            unit=baseline.get('unit', 'us'),
            description=baseline.get('description', '')
        )
        
        return ValidationResult(
            operation=result.operation,
            passed=len(violations) == 0,
            violations=violations,
            actual=result,
            baseline=baseline_result,
            thresholds=thresholds
        )
    
    def validate_all(self, results_file: str) -> List[ValidationResult]:
        """Validate all benchmark results"""
        results = self.load_benchmark_results(results_file)
        parsed_results = self.parse_benchmark_results(results)
        
        validation_results = []
        for result in parsed_results:
            validation_results.append(self.validate_operation(result))
        
        return validation_results
    
    def print_report(self, validation_results: List[ValidationResult]):
        """Print performance validation report"""
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("⚡ PERFORMANCE QUALITY GATE REPORT")
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("")
        
        passed = 0
        failed = 0
        skipped = 0
        
        for result in validation_results:
            if not result.baseline.operation:  # Skipped
                skipped += 1
                print(f"⏭️  {result.operation}: SKIPPED (no baseline)")
                continue
            
            if result.passed:
                passed += 1
                print(f"✅ {result.operation}: PASSED")
                print(f"   p50: {result.actual.p50:.1f}us (baseline: {result.baseline.p50:.1f}us)")
                print(f"   p95: {result.actual.p95:.1f}us (baseline: {result.baseline.p95:.1f}us)")
                print(f"   p99: {result.actual.p99:.1f}us (baseline: {result.baseline.p99:.1f}us)")
            else:
                failed += 1
                print(f"❌ {result.operation}: FAILED")
                for violation in result.violations:
                    print(f"   {violation}")
            
            print("")
        
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print(f"📊 Summary: {passed} passed, {failed} failed, {skipped} skipped")
        
        if failed > 0:
            print("❌ Performance quality gate FAILED")
            print("   Some operations exceed performance thresholds")
            return False
        else:
            print("✅ Performance quality gate PASSED")
            print("   All operations within performance thresholds")
            return True

def main():
    parser = argparse.ArgumentParser(description='Validate benchmark results against performance baselines')
    parser.add_argument('results_file', help='Path to benchmark results JSON file')
    parser.add_argument('baseline_file', help='Path to performance baseline JSON file')
    
    args = parser.parse_args()
    
    try:
        guard = PerformanceGuard(args.baseline_file)
        validation_results = guard.validate_all(args.results_file)
        success = guard.print_report(validation_results)
        
        sys.exit(0 if success else 1)
        
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()