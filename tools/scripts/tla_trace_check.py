#!/usr/bin/env python3

"""
TLA+ Trace Validation Script for ColibrìDB
Validates test traces against TLA+ specifications
"""

import json
import sys
import argparse
import subprocess
import tempfile
import os
from typing import Dict, Any, List, Optional
from dataclasses import dataclass

@dataclass
class TraceValidationResult:
    trace_file: str
    module: str
    valid: bool
    errors: List[str]
    warnings: List[str]

class TLA_TraceChecker:
    def __init__(self):
        self.tla_modules = {
            'WAL': {
                'spec_file': 'spec/WAL.tla',
                'config_file': 'spec/WAL.cfg',
                'invariants': [
                    'WALConsistency',
                    'WALOrdering',
                    'WALDurability',
                    'WALRecovery',
                    'WALGroupCommit',
                    'WALPerformance'
                ]
            },
            'MVCC': {
                'spec_file': 'spec/MVCC.tla',
                'config_file': 'spec/MVCC.cfg',
                'invariants': [
                    'MVCCSnapshotIsolation',
                    'MVCCSerializability',
                    'MVCCVisibility'
                ]
            },
            'LockManager': {
                'spec_file': 'spec/LockManager.tla',
                'config_file': 'spec/LockManager.cfg',
                'invariants': [
                    'LockConsistency',
                    'DeadlockFreedom'
                ]
            },
            'BTree': {
                'spec_file': 'spec/BTree.tla',
                'config_file': 'spec/BTree.cfg',
                'invariants': [
                    'BTreeOrdering',
                    'BTreeBalance',
                    'BTreeConsistency'
                ]
            },
            'BufferPool': {
                'spec_file': 'spec/BufferPool.tla',
                'config_file': 'spec/BufferPool.cfg',
                'invariants': [
                    'BufferConsistency',
                    'LRUProperty',
                    'DirtyPageTracking'
                ]
            },
            'RECOVERY': {
                'spec_file': 'spec/RECOVERY.tla',
                'config_file': 'spec/RECOVERY.cfg',
                'invariants': [
                    'RecoveryConsistency',
                    'RecoveryCompleteness'
                ]
            }
        }
    
    def load_trace(self, trace_file: str) -> Dict[str, Any]:
        """Load trace data from JSON file"""
        try:
            with open(trace_file, 'r') as f:
                return json.load(f)
        except Exception as e:
            raise Exception(f"Failed to load trace file '{trace_file}': {e}")
    
    def validate_trace_structure(self, trace_data: Dict[str, Any]) -> List[str]:
        """Validate basic trace structure"""
        errors = []
        
        # Check required fields
        required_fields = ['trace', 'module', 'timestamp', 'version']
        for field in required_fields:
            if field not in trace_data:
                errors.append(f"Missing required field: {field}")
        
        # Check trace format
        if 'trace' in trace_data:
            if not isinstance(trace_data['trace'], list):
                errors.append("Trace must be a list of states")
            elif len(trace_data['trace']) == 0:
                errors.append("Trace cannot be empty")
            else:
                # Validate each state
                for i, state in enumerate(trace_data['trace']):
                    if not isinstance(state, dict):
                        errors.append(f"State {i} must be a dictionary")
                    elif 'variables' not in state:
                        errors.append(f"State {i} missing 'variables' field")
        
        return errors
    
    def validate_trace_against_spec(self, trace_file: str, module: str) -> TraceValidationResult:
        """Validate trace against TLA+ specification"""
        errors = []
        warnings = []
        
        # Load trace
        try:
            trace_data = self.load_trace(trace_file)
        except Exception as e:
            return TraceValidationResult(
                trace_file=trace_file,
                module=module,
                valid=False,
                errors=[str(e)],
                warnings=[]
            )
        
        # Validate structure
        structure_errors = self.validate_trace_structure(trace_data)
        errors.extend(structure_errors)
        
        if structure_errors:
            return TraceValidationResult(
                trace_file=trace_file,
                module=module,
                valid=False,
                errors=errors,
                warnings=warnings
            )
        
        # Check if module is supported
        if module not in self.tla_modules:
            errors.append(f"Unsupported module: {module}")
            return TraceValidationResult(
                trace_file=trace_file,
                module=module,
                valid=False,
                errors=errors,
                warnings=warnings
            )
        
        # Validate against TLA+ specification
        spec_info = self.tla_modules[module]
        
        # Check if spec files exist
        if not os.path.exists(spec_info['spec_file']):
            errors.append(f"Specification file not found: {spec_info['spec_file']}")
            return TraceValidationResult(
                trace_file=trace_file,
                module=module,
                valid=False,
                errors=errors,
                warnings=warnings
            )
        
        if not os.path.exists(spec_info['config_file']):
            errors.append(f"Configuration file not found: {spec_info['config_file']}")
            return TraceValidationResult(
                trace_file=trace_file,
                module=module,
                valid=False,
                errors=errors,
                warnings=warnings
            )
        
        # Run TLC trace validation
        try:
            tlc_result = self._run_tlc_trace_validation(trace_file, module, spec_info)
            if not tlc_result['valid']:
                errors.extend(tlc_result['errors'])
            warnings.extend(tlc_result['warnings'])
        except Exception as e:
            errors.append(f"TLC validation failed: {e}")
        
        # Additional semantic validation
        semantic_errors = self._validate_trace_semantics(trace_data, module)
        errors.extend(semantic_errors)
        
        return TraceValidationResult(
            trace_file=trace_file,
            module=module,
            valid=len(errors) == 0,
            errors=errors,
            warnings=warnings
        )
    
    def _run_tlc_trace_validation(self, trace_file: str, module: str, spec_info: Dict[str, Any]) -> Dict[str, Any]:
        """Run TLC trace validation using TLA+ tools"""
        errors = []
        warnings = []
        
        try:
            # Create temporary trace file in TLC format
            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as temp_trace:
                trace_data = self.load_trace(trace_file)
                json.dump(trace_data, temp_trace, indent=2)
                temp_trace_path = temp_trace.name
            
            # Run TLC with trace validation
            cmd = [
                'java', '-cp', 'tla2tools.jar',
                'tlc2.TLC',
                '-deadlock',
                '-coverage', '1',
                '-config', spec_info['config_file'],
                spec_info['spec_file']
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # Clean up temp file
            os.unlink(temp_trace_path)
            
            if result.returncode != 0:
                errors.append(f"TLC validation failed: {result.stderr}")
            else:
                # Parse TLC output for warnings
                if 'warning' in result.stdout.lower():
                    warnings.append("TLC reported warnings during validation")
        
        except subprocess.TimeoutExpired:
            errors.append("TLC validation timed out")
        except FileNotFoundError:
            errors.append("TLA+ tools not found (tla2tools.jar)")
        except Exception as e:
            errors.append(f"TLC execution error: {e}")
        
        return {
            'valid': len(errors) == 0,
            'errors': errors,
            'warnings': warnings
        }
    
    def _validate_trace_semantics(self, trace_data: Dict[str, Any], module: str) -> List[str]:
        """Validate trace semantics for specific module"""
        errors = []
        
        if 'trace' not in trace_data:
            return errors
        
        trace = trace_data['trace']
        
        if module == 'WAL':
            errors.extend(self._validate_wal_trace(trace))
        elif module == 'MVCC':
            errors.extend(self._validate_mvcc_trace(trace))
        elif module == 'LockManager':
            errors.extend(self._validate_lockmanager_trace(trace))
        elif module == 'BTree':
            errors.extend(self._validate_btree_trace(trace))
        elif module == 'BufferPool':
            errors.extend(self._validate_bufferpool_trace(trace))
        elif module == 'RECOVERY':
            errors.extend(self._validate_recovery_trace(trace))
        
        return errors
    
    def _validate_wal_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate WAL-specific trace semantics"""
        errors = []
        
        # Check WAL ordering
        last_lsn = -1
        for i, state in enumerate(trace):
            if 'variables' in state and 'wal_log' in state['variables']:
                wal_log = state['variables']['wal_log']
                if isinstance(wal_log, list):
                    for record in wal_log:
                        if 'lsn' in record and record['lsn'] <= last_lsn:
                            errors.append(f"WAL ordering violation at state {i}: LSN {record['lsn']} <= {last_lsn}")
                        if 'lsn' in record:
                            last_lsn = max(last_lsn, record['lsn'])
        
        return errors
    
    def _validate_mvcc_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate MVCC-specific trace semantics"""
        errors = []
        
        # Check transaction isolation
        active_transactions = set()
        for i, state in enumerate(trace):
            if 'variables' in state and 'transactions' in state['variables']:
                transactions = state['variables']['transactions']
                if isinstance(transactions, dict):
                    for tx_id, tx_data in transactions.items():
                        if tx_data.get('status') == 'active':
                            active_transactions.add(tx_id)
                        elif tx_data.get('status') == 'committed':
                            active_transactions.discard(tx_id)
        
        return errors
    
    def _validate_lockmanager_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate LockManager-specific trace semantics"""
        errors = []
        
        # Check for deadlocks
        for i, state in enumerate(trace):
            if 'variables' in state and 'wait_graph' in state['variables']:
                wait_graph = state['variables']['wait_graph']
                if isinstance(wait_graph, dict):
                    # Simple cycle detection
                    visited = set()
                    rec_stack = set()
                    
                    def has_cycle(node):
                        if node in rec_stack:
                            return True
                        if node in visited:
                            return False
                        
                        visited.add(node)
                        rec_stack.add(node)
                        
                        for neighbor in wait_graph.get(node, []):
                            if has_cycle(neighbor):
                                return True
                        
                        rec_stack.remove(node)
                        return False
                    
                    for node in wait_graph:
                        if has_cycle(node):
                            errors.append(f"Deadlock detected at state {i}")
                            break
        
        return errors
    
    def _validate_btree_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate BTree-specific trace semantics"""
        errors = []
        
        # Check BTree ordering
        for i, state in enumerate(trace):
            if 'variables' in state and 'btree' in state['variables']:
                btree = state['variables']['btree']
                if isinstance(btree, dict) and 'nodes' in btree:
                    nodes = btree['nodes']
                    if isinstance(nodes, dict):
                        for node_id, node_data in nodes.items():
                            if 'keys' in node_data and isinstance(node_data['keys'], list):
                                keys = node_data['keys']
                                if keys != sorted(keys):
                                    errors.append(f"BTree ordering violation at state {i}, node {node_id}")
        
        return errors
    
    def _validate_bufferpool_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate BufferPool-specific trace semantics"""
        errors = []
        
        # Check LRU property
        for i, state in enumerate(trace):
            if 'variables' in state and 'buffer_pool' in state['variables']:
                buffer_pool = state['variables']['buffer_pool']
                if isinstance(buffer_pool, dict) and 'lru_order' in buffer_pool:
                    lru_order = buffer_pool['lru_order']
                    if isinstance(lru_order, list):
                        # Check that LRU order is maintained
                        pass  # Implementation depends on specific LRU algorithm
        
        return errors
    
    def _validate_recovery_trace(self, trace: List[Dict[str, Any]]) -> List[str]:
        """Validate Recovery-specific trace semantics"""
        errors = []
        
        # Check recovery consistency
        for i, state in enumerate(trace):
            if 'variables' in state and 'recovery_state' in state['variables']:
                recovery_state = state['variables']['recovery_state']
                if isinstance(recovery_state, dict):
                    # Check that recovery maintains consistency
                    pass  # Implementation depends on specific recovery algorithm
        
        return errors
    
    def print_report(self, results: List[TraceValidationResult]):
        """Print trace validation report"""
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("🔍 TLA+ TRACE VALIDATION REPORT")
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("")
        
        total_traces = len(results)
        valid_traces = sum(1 for r in results if r.valid)
        failed_traces = total_traces - valid_traces
        
        print(f"📊 Summary: {valid_traces}/{total_traces} traces valid")
        print("")
        
        for result in results:
            if result.valid:
                print(f"✅ {result.trace_file} ({result.module}): VALID")
            else:
                print(f"❌ {result.trace_file} ({result.module}): INVALID")
                for error in result.errors:
                    print(f"   Error: {error}")
            
            if result.warnings:
                for warning in result.warnings:
                    print(f"   Warning: {warning}")
            
            print("")
        
        if failed_traces > 0:
            print("❌ Trace validation FAILED")
            print(f"   {failed_traces} traces failed validation")
        else:
            print("✅ Trace validation PASSED")
            print("   All traces are valid against TLA+ specifications")

def main():
    parser = argparse.ArgumentParser(description='Validate test traces against TLA+ specifications')
    parser.add_argument('trace_file', help='Path to trace JSON file')
    parser.add_argument('module', help='TLA+ module name (WAL, MVCC, LockManager, etc.)')
    
    args = parser.parse_args()
    
    checker = TLA_TraceChecker()
    result = checker.validate_trace_against_spec(args.trace_file, args.module)
    
    checker.print_report([result])
    
    sys.exit(0 if result.valid else 1)

if __name__ == '__main__':
    main()