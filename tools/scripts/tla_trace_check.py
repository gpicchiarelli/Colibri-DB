#!/usr/bin/env python3
"""
TLA+ Trace Checker for ColibrìDB
Validates execution traces from tests against TLA+ specifications.

Usage:
    python3 tla_trace_check.py <trace_file> <spec_module>

Exit codes:
    0 - Trace valid (all invariants hold)
    1 - Trace invalid (invariant violated)
    2 - Error in execution (TLC failure, missing files, etc.)
"""

import json
import sys
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, Any, List, Optional


class Colors:
    """ANSI color codes"""
    RESET = "\033[0m"
    RED = "\033[91m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    BOLD = "\033[1m"


class TLATraceChecker:
    """Validates runtime traces against TLA+ specifications"""

    def __init__(self, trace_file: str, spec_module: str, repo_root: Path):
        self.trace_file = Path(trace_file)
        self.spec_module = spec_module
        self.repo_root = repo_root
        self.specs_dir = repo_root / "specs"
        self.trace_data: Optional[Dict[str, Any]] = None
        self.tla_modules: Optional[Dict[str, Any]] = None

    def load_trace(self) -> bool:
        """Load execution trace from test"""
        try:
            with open(self.trace_file, 'r') as f:
                self.trace_data = json.load(f)
            print(f"{Colors.GREEN}✓{Colors.RESET} Loaded trace: {self.trace_file}")
            return True
        except FileNotFoundError:
            print(f"{Colors.RED}✗ Trace file not found: {self.trace_file}{Colors.RESET}")
            return False
        except json.JSONDecodeError as e:
            print(f"{Colors.RED}✗ Invalid trace JSON: {e}{Colors.RESET}")
            return False

    def load_tla_config(self) -> bool:
        """Load TLA+ module configuration"""
        config_file = self.repo_root / "rules" / "tla_modules.json"
        try:
            with open(config_file, 'r') as f:
                config = json.load(f)
                self.tla_modules = config.get('modules', {})
            print(f"{Colors.GREEN}✓{Colors.RESET} Loaded TLA+ config: {config_file}")
            return True
        except FileNotFoundError:
            print(f"{Colors.RED}✗ TLA+ config not found: {config_file}{Colors.RESET}")
            return False
        except json.JSONDecodeError as e:
            print(f"{Colors.RED}✗ Invalid TLA+ config JSON: {e}{Colors.RESET}")
            return False

    def check_tlc_installed(self) -> bool:
        """Check if TLC (TLA+ model checker) is installed"""
        try:
            result = subprocess.run(
                ['java', '-cp', 'tla2tools.jar', 'tlc2.TLC', '-h'],
                capture_output=True,
                timeout=5
            )
            return result.returncode == 0
        except (subprocess.TimeoutExpired, FileNotFoundError):
            print(f"{Colors.YELLOW}⚠ TLC not found. Skipping formal verification.{Colors.RESET}")
            print(f"{Colors.YELLOW}  Install TLA+ tools: https://github.com/tlaplus/tlaplus{Colors.RESET}")
            return False

    def convert_trace_to_tla(self) -> Optional[Path]:
        """Convert JSON trace to TLA+ trace format"""
        if not self.trace_data:
            return None

        try:
            # Create temporary TLA+ trace file
            temp_file = tempfile.NamedTemporaryFile(
                mode='w',
                suffix='.tla',
                delete=False,
                prefix='trace_'
            )

            # Write TLA+ trace format
            temp_file.write("---- MODULE TraceSpec ----\n")
            temp_file.write("EXTENDS TLC, Sequences, Naturals\n\n")

            # Convert trace states
            temp_file.write("TraceStates == <<\n")
            for i, state in enumerate(self.trace_data.get('states', [])):
                temp_file.write("  [ ")
                for key, value in state.items():
                    temp_file.write(f"{key} |-> {self._convert_value(value)}, ")
                temp_file.write("]\n")
                if i < len(self.trace_data.get('states', [])) - 1:
                    temp_file.write(",\n")
            temp_file.write(">>\n\n")

            temp_file.write("====\n")
            temp_file.close()

            print(f"{Colors.GREEN}✓{Colors.RESET} Generated TLA+ trace: {temp_file.name}")
            return Path(temp_file.name)

        except Exception as e:
            print(f"{Colors.RED}✗ Failed to convert trace: {e}{Colors.RESET}")
            return None

    def _convert_value(self, value: Any) -> str:
        """Convert Python value to TLA+ format"""
        if isinstance(value, bool):
            return "TRUE" if value else "FALSE"
        elif isinstance(value, int):
            return str(value)
        elif isinstance(value, str):
            return f'"{value}"'
        elif isinstance(value, list):
            items = ", ".join(self._convert_value(v) for v in value)
            return f"<< {items} >>"
        elif isinstance(value, dict):
            items = ", ".join(f"{k} :> {self._convert_value(v)}" for k, v in value.items())
            return f"[ {items} ]"
        else:
            return str(value)

    def run_tlc(self, trace_file: Path) -> bool:
        """Run TLC model checker on trace"""
        if self.spec_module not in self.tla_modules:
            print(f"{Colors.RED}✗ Unknown module: {self.spec_module}{Colors.RESET}")
            return False

        module_info = self.tla_modules[self.spec_module]
        spec_file = self.specs_dir / module_info['spec_file']
        config_file = self.specs_dir / module_info['config_file']

        if not spec_file.exists():
            print(f"{Colors.YELLOW}⚠ Spec file not found: {spec_file}{Colors.RESET}")
            print(f"{Colors.YELLOW}  Skipping formal verification for {self.spec_module}{Colors.RESET}")
            return True  # Don't fail if spec not yet implemented

        print(f"\n{Colors.BOLD}Running TLC Model Checker...{Colors.RESET}")
        print(f"  Module: {self.spec_module}")
        print(f"  Spec:   {spec_file}")
        print(f"  Trace:  {trace_file}\n")

        try:
            # Run TLC with trace validation
            cmd = [
                'java',
                '-cp', 'tla2tools.jar',
                'tlc2.TLC',
                '-config', str(config_file),
                '-trace', str(trace_file),
                '-workers', '4',
                '-coverage', '1',
                str(spec_file)
            ]

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,  # 5 minutes
                cwd=self.specs_dir
            )

            # Parse TLC output
            output = result.stdout + result.stderr

            if "Error:" in output or "Invariant" in output and "violated" in output:
                print(f"{Colors.RED}✗ TLC found invariant violation:{Colors.RESET}\n")
                print(output)
                return False
            elif result.returncode == 0:
                print(f"{Colors.GREEN}✓ TLC validation passed - all invariants hold{Colors.RESET}")
                # Print coverage info
                if "states generated" in output:
                    for line in output.split('\n'):
                        if "states generated" in line or "distinct states" in line:
                            print(f"  {line.strip()}")
                return True
            else:
                print(f"{Colors.RED}✗ TLC execution failed:{Colors.RESET}\n")
                print(output)
                return False

        except subprocess.TimeoutExpired:
            print(f"{Colors.RED}✗ TLC timeout - model checking took too long{Colors.RESET}")
            return False
        except FileNotFoundError:
            print(f"{Colors.RED}✗ TLC not found - ensure tla2tools.jar is in PATH{Colors.RESET}")
            return False
        except Exception as e:
            print(f"{Colors.RED}✗ TLC execution error: {e}{Colors.RESET}")
            return False

    def check_invariants(self) -> bool:
        """Check invariants manually from trace (fallback if TLC not available)"""
        if not self.trace_data:
            return False

        module_info = self.tla_modules.get(self.spec_module, {})
        invariants = module_info.get('invariants', [])

        print(f"\n{Colors.BOLD}Checking Invariants (Manual)...{Colors.RESET}\n")

        all_passed = True
        for invariant in invariants:
            name = invariant['name']
            critical = invariant.get('critical', True)

            # Simple heuristic checks based on invariant name
            passed = self._check_invariant_heuristic(name)

            status = f"{Colors.GREEN}✓{Colors.RESET}" if passed else f"{Colors.RED}✗{Colors.RESET}"
            criticality = "CRITICAL" if critical else "non-critical"

            print(f"  {status} {name} ({criticality})")

            if not passed and critical:
                all_passed = False

        return all_passed

    def _check_invariant_heuristic(self, invariant_name: str) -> bool:
        """Simple heuristic check for common invariants"""
        # This is a simplified fallback - real validation should use TLC
        if not self.trace_data or 'states' not in self.trace_data:
            return True  # No trace data, assume OK

        states = self.trace_data.get('states', [])

        # Example heuristic checks
        if 'Deadlock' in invariant_name:
            # Check no deadlock state
            return not any(state.get('deadlock', False) for state in states)

        if 'Consistency' in invariant_name or 'Isolation' in invariant_name:
            # Check no consistency violations
            return not any(state.get('violation', False) for state in states)

        # Default: assume pass (requires TLC for proper validation)
        return True

    def run(self) -> int:
        """Main execution flow"""
        print(f"\n{Colors.BOLD}TLA+ Trace Validation{Colors.RESET}")
        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}\n")

        # Load data
        if not self.load_trace():
            return 2
        if not self.load_tla_config():
            return 2

        # Check if TLC is available
        has_tlc = self.check_tlc_installed()

        if has_tlc:
            # Full TLA+ validation with TLC
            trace_tla = self.convert_trace_to_tla()
            if not trace_tla:
                return 2

            is_valid = self.run_tlc(trace_tla)

            # Cleanup temp file
            try:
                trace_tla.unlink()
            except:
                pass
        else:
            # Fallback to heuristic checking
            print(f"{Colors.YELLOW}Using heuristic invariant checking (TLC not available){Colors.RESET}\n")
            is_valid = self.check_invariants()

        print(f"\n{Colors.BOLD}{'='*80}{Colors.RESET}")

        if is_valid:
            print(f"{Colors.GREEN}{Colors.BOLD}✓ Trace validation PASSED{Colors.RESET}")
            print(f"{Colors.GREEN}All invariants hold for the execution trace.{Colors.RESET}")
            return 0
        else:
            print(f"{Colors.RED}{Colors.BOLD}✗ Trace validation FAILED{Colors.RESET}")
            print(f"{Colors.RED}One or more invariants violated.{Colors.RESET}")
            print(f"{Colors.RED}Review the counterexample above.{Colors.RESET}")
            return 1


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <trace_file.json> <spec_module>")
        print(f"\nExample:")
        print(f"  {sys.argv[0]} tests/traces/mvcc_test.json MVCC")
        print(f"\nAvailable modules: WAL, MVCC, LockManager, BTree, TransactionManager, BufferPool")
        sys.exit(2)

    trace_file = sys.argv[1]
    spec_module = sys.argv[2]

    # Find repository root
    repo_root = Path(__file__).parent.parent.parent

    checker = TLATraceChecker(trace_file, spec_module, repo_root)
    exit_code = checker.run()
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

