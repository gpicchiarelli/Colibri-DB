#!/usr/bin/env python3
"""
Performance Guard for ColibrìDB
Validates benchmark results against performance baselines.
Fails CI if performance degrades beyond tolerance.

Usage:
    python3 perf_guard.py <benchmark_results.json> <baseline.json>

Exit codes:
    0 - All checks passed
    1 - Performance degradation detected
    2 - Missing data or parse error
"""

import json
import sys
from typing import Dict, Any, List, Tuple
from pathlib import Path


class Colors:
    """ANSI color codes for terminal output"""
    RESET = "\033[0m"
    RED = "\033[91m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    BOLD = "\033[1m"


class PerfGuard:
    def __init__(self, results_file: str, baseline_file: str):
        self.results_file = Path(results_file)
        self.baseline_file = Path(baseline_file)
        self.results: Dict[str, Any] = {}
        self.baseline: Dict[str, Any] = {}
        self.failures: List[Tuple[str, str, float, float, float]] = []
        self.warnings: List[Tuple[str, str, float, float, float]] = []
        self.passes: List[Tuple[str, str, float, float]] = []

    def load_data(self) -> bool:
        """Load benchmark results and baseline data"""
        try:
            with open(self.baseline_file, 'r') as f:
                self.baseline = json.load(f)
            print(f"{Colors.GREEN}✓{Colors.RESET} Loaded baseline: {self.baseline_file}")
        except FileNotFoundError:
            print(f"{Colors.RED}✗ Baseline file not found: {self.baseline_file}{Colors.RESET}")
            return False
        except json.JSONDecodeError as e:
            print(f"{Colors.RED}✗ Invalid baseline JSON: {e}{Colors.RESET}")
            return False

        try:
            with open(self.results_file, 'r') as f:
                self.results = json.load(f)
            print(f"{Colors.GREEN}✓{Colors.RESET} Loaded results: {self.results_file}")
        except FileNotFoundError:
            print(f"{Colors.RED}✗ Results file not found: {self.results_file}{Colors.RESET}")
            return False
        except json.JSONDecodeError as e:
            print(f"{Colors.RED}✗ Invalid results JSON: {e}{Colors.RESET}")
            return False

        return True

    def get_tolerance(self, percentile: str) -> float:
        """Get tolerance threshold for a given percentile"""
        tolerance_map = {
            'p50': self.baseline.get('tolerance', {}).get('p50', 0.05),
            'p95': self.baseline.get('tolerance', {}).get('p95', 0.10),
            'p99': self.baseline.get('tolerance', {}).get('p99', 0.15),
        }
        return tolerance_map.get(percentile, 0.10)

    def check_operation(self, category: str, operation: str, op_baseline: Dict[str, Any]) -> None:
        """Check a single operation against its baseline"""
        op_key = f"{category}.{operation}"
        
        # Try to find results in the benchmark output
        op_results = self.results.get('operations', {}).get(category, {}).get(operation, {})
        
        if not op_results:
            # Operation not found in results, skip
            return

        for percentile in ['p50', 'p95', 'p99']:
            baseline_value = op_baseline.get(percentile)
            actual_value = op_results.get(percentile)

            if baseline_value is None or actual_value is None:
                continue

            tolerance = self.get_tolerance(percentile)
            max_allowed = baseline_value * (1 + tolerance)
            degradation_pct = ((actual_value - baseline_value) / baseline_value) * 100

            metric_name = f"{op_key}.{percentile}"

            if actual_value > max_allowed:
                # Performance degradation
                self.failures.append((
                    metric_name,
                    op_baseline.get('unit', 'us'),
                    baseline_value,
                    actual_value,
                    degradation_pct
                ))
            elif actual_value > baseline_value:
                # Minor degradation within tolerance
                self.warnings.append((
                    metric_name,
                    op_baseline.get('unit', 'us'),
                    baseline_value,
                    actual_value,
                    degradation_pct
                ))
            else:
                # Performance improvement or stable
                self.passes.append((
                    metric_name,
                    op_baseline.get('unit', 'us'),
                    baseline_value,
                    actual_value
                ))

    def validate(self) -> bool:
        """Validate all operations against baselines"""
        print(f"\n{Colors.BOLD}Running Performance Validation...{Colors.RESET}\n")

        operations = self.baseline.get('operations', {})
        
        for category, ops in operations.items():
            for operation, op_baseline in ops.items():
                self.check_operation(category, operation, op_baseline)

        return len(self.failures) == 0

    def print_report(self) -> None:
        """Print detailed validation report"""
        print(f"\n{Colors.BOLD}{'='*80}{Colors.RESET}")
        print(f"{Colors.BOLD}Performance Guard Report{Colors.RESET}")
        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}\n")

        # Failures
        if self.failures:
            print(f"{Colors.RED}{Colors.BOLD}✗ FAILURES ({len(self.failures)}){Colors.RESET}")
            print(f"{Colors.RED}Performance degraded beyond tolerance:{Colors.RESET}\n")
            for metric, unit, baseline, actual, degradation in self.failures:
                print(f"  {Colors.RED}✗{Colors.RESET} {metric}")
                print(f"    Baseline: {baseline:.2f} {unit}")
                print(f"    Actual:   {actual:.2f} {unit}")
                print(f"    Degradation: {Colors.RED}+{degradation:.1f}%{Colors.RESET}")
                print()

        # Warnings
        if self.warnings:
            print(f"{Colors.YELLOW}{Colors.BOLD}⚠ WARNINGS ({len(self.warnings)}){Colors.RESET}")
            print(f"{Colors.YELLOW}Performance degraded within tolerance:{Colors.RESET}\n")
            for metric, unit, baseline, actual, degradation in self.warnings:
                print(f"  {Colors.YELLOW}⚠{Colors.RESET} {metric}")
                print(f"    Baseline: {baseline:.2f} {unit}")
                print(f"    Actual:   {actual:.2f} {unit}")
                print(f"    Degradation: {Colors.YELLOW}+{degradation:.1f}%{Colors.RESET}")
                print()

        # Passes
        if self.passes:
            print(f"{Colors.GREEN}{Colors.BOLD}✓ PASSED ({len(self.passes)}){Colors.RESET}")
            improvements = [(m, u, b, a) for m, u, b, a in self.passes if a < b]
            stable = [(m, u, b, a) for m, u, b, a in self.passes if a >= b]

            if improvements:
                print(f"{Colors.GREEN}Performance improved:{Colors.RESET}\n")
                for metric, unit, baseline, actual in improvements[:5]:  # Show top 5
                    improvement_pct = ((baseline - actual) / baseline) * 100
                    print(f"  {Colors.GREEN}✓{Colors.RESET} {metric}")
                    print(f"    Baseline: {baseline:.2f} {unit}")
                    print(f"    Actual:   {actual:.2f} {unit}")
                    print(f"    Improvement: {Colors.GREEN}-{improvement_pct:.1f}%{Colors.RESET}")
                    print()

                if len(improvements) > 5:
                    print(f"  ... and {len(improvements) - 5} more improvements\n")

            if stable:
                print(f"{Colors.GREEN}Performance stable: {len(stable)} metrics{Colors.RESET}\n")

        # Summary
        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}")
        total = len(self.failures) + len(self.warnings) + len(self.passes)
        print(f"{Colors.BOLD}Summary:{Colors.RESET}")
        print(f"  Total metrics checked: {total}")
        print(f"  {Colors.GREEN}Passed: {len(self.passes)}{Colors.RESET}")
        print(f"  {Colors.YELLOW}Warnings: {len(self.warnings)}{Colors.RESET}")
        print(f"  {Colors.RED}Failures: {len(self.failures)}{Colors.RESET}")
        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}\n")

    def run(self) -> int:
        """Main execution flow"""
        if not self.load_data():
            return 2

        is_valid = self.validate()
        self.print_report()

        if is_valid:
            print(f"{Colors.GREEN}{Colors.BOLD}✓ Performance guard PASSED{Colors.RESET}")
            return 0
        else:
            print(f"{Colors.RED}{Colors.BOLD}✗ Performance guard FAILED{Colors.RESET}")
            print(f"{Colors.RED}Performance has degraded beyond acceptable limits.{Colors.RESET}")
            print(f"{Colors.RED}Please investigate and optimize before merging.{Colors.RESET}")
            return 1


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <benchmark_results.json> <baseline.json>")
        print(f"\nExample:")
        print(f"  {sys.argv[0]} results.json rules/perf_baseline.json")
        sys.exit(2)

    results_file = sys.argv[1]
    baseline_file = sys.argv[2]

    guard = PerfGuard(results_file, baseline_file)
    exit_code = guard.run()
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

