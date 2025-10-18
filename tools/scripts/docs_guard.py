#!/usr/bin/env python3
"""
Documentation Guard for ColibrìDB
Ensures critical modules have up-to-date documentation when modified.

Checks:
1. If critical source file changed → corresponding docs must be updated
2. Public API changes → API docs must be updated
3. New critical features → must have documentation

Usage:
    python3 docs_guard.py <changed_files.txt>

Exit codes:
    0 - All checks passed
    1 - Documentation updates required
    2 - Error in execution
"""

import sys
import re
from pathlib import Path
from typing import List, Set, Dict, Tuple


class Colors:
    """ANSI color codes"""
    RESET = "\033[0m"
    RED = "\033[91m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    BOLD = "\033[1m"


class DocsGuard:
    """Documentation guard for critical modules"""

    # Critical modules that require documentation
    CRITICAL_MODULES = {
        'Storage/WAL': {
            'sources': ['Sources/ColibriCore/Storage/WAL/'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/01-WAL-and-Recovery.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'Write-Ahead Log and Recovery'
        },
        'Concurrency/MVCC': {
            'sources': ['Sources/ColibriCore/Concurrency/Transactions/MVCC.swift'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/05-MVCC-Concurrency.md',
                'docs/wiki/Part-01-Foundations/03-Transactions-Theory.md'
            ],
            'description': 'Multi-Version Concurrency Control'
        },
        'Concurrency/LockManager': {
            'sources': ['Sources/ColibriCore/Concurrency/Transactions/LockManager.swift'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/05-MVCC-Concurrency.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'Lock Manager and Deadlock Detection'
        },
        'Storage/BTree': {
            'sources': ['Sources/ColibriCore/Storage/Index/BTree'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/04-BTree-Indexes.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'B-Tree Index Implementation'
        },
        'Storage/Pager': {
            'sources': ['Sources/ColibriCore/Storage/Pager/'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/03-Heap-Storage.md',
                'docs/wiki/Part-01-Foundations/04-Storage-Principles.md'
            ],
            'description': 'Page Management and Storage'
        },
        'Storage/BufferPool': {
            'sources': ['Sources/ColibriCore/Storage/Buffer/'],
            'docs': [
                'docs/wiki/Part-02-Core-Engine/02-BufferPool.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'Buffer Pool and Caching'
        },
        'Query/Parser': {
            'sources': ['Sources/ColibriCore/Query/Parser/'],
            'docs': [
                'docs/wiki/Part-03-Query/01-SQL-Parser.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'SQL Parser'
        },
        'Query/Planner': {
            'sources': ['Sources/ColibriCore/Query/Planner/'],
            'docs': [
                'docs/wiki/Part-03-Query/02-Logical-Planning.md',
                'docs/wiki/Part-03-Query/03-Physical-Planning.md',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'Query Planning and Optimization'
        },
        'System/Catalog': {
            'sources': ['Sources/ColibriCore/System/Catalog/'],
            'docs': [
                'docs/wiki/Part-04-Metadata/',
                'docs/wiki/API-Reference.md'
            ],
            'description': 'System Catalog and Metadata'
        }
    }

    def __init__(self, changed_files: List[str], repo_root: Path):
        self.changed_files = changed_files
        self.repo_root = repo_root
        self.violations: List[Tuple[str, List[str], str]] = []
        self.warnings: List[Tuple[str, str]] = []

    def is_source_file(self, file_path: str) -> bool:
        """Check if file is a source code file"""
        return file_path.endswith('.swift') and 'Sources/ColibriCore' in file_path

    def is_doc_file(self, file_path: str) -> bool:
        """Check if file is a documentation file"""
        return file_path.endswith('.md') and 'docs/wiki' in file_path

    def find_affected_modules(self) -> Dict[str, List[str]]:
        """Find which critical modules were affected by changes"""
        affected = {}

        for file_path in self.changed_files:
            if not self.is_source_file(file_path):
                continue

            for module_name, module_info in self.CRITICAL_MODULES.items():
                for source_pattern in module_info['sources']:
                    if source_pattern in file_path:
                        if module_name not in affected:
                            affected[module_name] = []
                        affected[module_name].append(file_path)
                        break

        return affected

    def find_updated_docs(self) -> Set[str]:
        """Find which documentation files were updated"""
        updated_docs = set()

        for file_path in self.changed_files:
            if self.is_doc_file(file_path):
                updated_docs.add(file_path)

        return updated_docs

    def check_module_docs(self, module_name: str, changed_sources: List[str]) -> bool:
        """Check if module documentation was updated"""
        module_info = self.CRITICAL_MODULES[module_name]
        required_docs = module_info['docs']
        updated_docs = self.find_updated_docs()

        # Check if any of the required docs were updated
        docs_updated = False
        for required_doc in required_docs:
            # Check if any updated doc matches or is within the required doc path
            for updated_doc in updated_docs:
                if required_doc in updated_doc or updated_doc in required_doc:
                    docs_updated = True
                    break
            if docs_updated:
                break

        if not docs_updated:
            self.violations.append((
                module_name,
                required_docs,
                module_info['description']
            ))
            return False

        return True

    def check_api_changes(self) -> None:
        """Check for public API changes that need documentation"""
        api_pattern = re.compile(r'^\s*public\s+(class|struct|enum|protocol|func|var|let)')

        for file_path in self.changed_files:
            if not self.is_source_file(file_path):
                continue

            full_path = self.repo_root / file_path
            if not full_path.exists():
                continue

            try:
                with open(full_path, 'r') as f:
                    content = f.read()
                    if api_pattern.search(content):
                        self.warnings.append((
                            file_path,
                            "Contains public API - ensure API-Reference.md is updated"
                        ))
            except Exception as e:
                print(f"{Colors.YELLOW}Warning: Could not read {file_path}: {e}{Colors.RESET}")

    def validate(self) -> bool:
        """Run all documentation checks"""
        print(f"\n{Colors.BOLD}Running Documentation Guard...{Colors.RESET}\n")

        affected_modules = self.find_affected_modules()

        if not affected_modules:
            print(f"{Colors.GREEN}✓ No critical modules modified{Colors.RESET}")
            return True

        print(f"{Colors.BLUE}Critical modules affected: {len(affected_modules)}{Colors.RESET}")
        for module_name in affected_modules.keys():
            print(f"  • {module_name}")
        print()

        all_passed = True
        for module_name, changed_sources in affected_modules.items():
            passed = self.check_module_docs(module_name, changed_sources)
            if not passed:
                all_passed = False

        # Check for API changes
        self.check_api_changes()

        return all_passed

    def print_report(self) -> None:
        """Print validation report"""
        print(f"\n{Colors.BOLD}{'='*80}{Colors.RESET}")
        print(f"{Colors.BOLD}Documentation Guard Report{Colors.RESET}")
        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}\n")

        if self.violations:
            print(f"{Colors.RED}{Colors.BOLD}✗ VIOLATIONS ({len(self.violations)}){Colors.RESET}")
            print(f"{Colors.RED}Critical modules modified without documentation updates:{Colors.RESET}\n")

            for module_name, required_docs, description in self.violations:
                print(f"  {Colors.RED}✗{Colors.RESET} {Colors.BOLD}{module_name}{Colors.RESET}")
                print(f"    Description: {description}")
                print(f"    Required documentation updates:")
                for doc in required_docs:
                    print(f"      • {doc}")
                print()

        if self.warnings:
            print(f"{Colors.YELLOW}{Colors.BOLD}⚠ WARNINGS ({len(self.warnings)}){Colors.RESET}\n")
            for file_path, message in self.warnings:
                print(f"  {Colors.YELLOW}⚠{Colors.RESET} {file_path}")
                print(f"    {message}\n")

        if not self.violations and not self.warnings:
            print(f"{Colors.GREEN}✓ All documentation checks passed{Colors.RESET}\n")

        print(f"{Colors.BOLD}{'='*80}{Colors.RESET}\n")

    def run(self) -> int:
        """Main execution"""
        is_valid = self.validate()
        self.print_report()

        if is_valid:
            print(f"{Colors.GREEN}{Colors.BOLD}✓ Documentation guard PASSED{Colors.RESET}")
            return 0
        else:
            print(f"{Colors.RED}{Colors.BOLD}✗ Documentation guard FAILED{Colors.RESET}")
            print(f"{Colors.RED}Please update the required documentation before merging.{Colors.RESET}")
            print(f"{Colors.YELLOW}Tip: Documentation should explain what changed and why.{Colors.RESET}")
            return 1


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <changed_files.txt>")
        print(f"\nExample:")
        print(f"  git diff --name-only origin/main > changed.txt")
        print(f"  {sys.argv[0]} changed.txt")
        sys.exit(2)

    changed_files_path = Path(sys.argv[1])

    if not changed_files_path.exists():
        print(f"{Colors.RED}Error: File not found: {changed_files_path}{Colors.RESET}")
        sys.exit(2)

    try:
        with open(changed_files_path, 'r') as f:
            changed_files = [line.strip() for line in f if line.strip()]
    except Exception as e:
        print(f"{Colors.RED}Error reading file: {e}{Colors.RESET}")
        sys.exit(2)

    # Find repository root (assume script is in tools/scripts/)
    repo_root = Path(__file__).parent.parent.parent

    guard = DocsGuard(changed_files, repo_root)
    exit_code = guard.run()
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

