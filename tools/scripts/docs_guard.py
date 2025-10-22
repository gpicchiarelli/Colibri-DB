#!/usr/bin/env python3

"""
Documentation Guard Script for ColibrìDB
Validates documentation quality and completeness
"""

import os
import sys
import argparse
from typing import List, Set, Dict, Any
from pathlib import Path
import re

class DocumentationGuard:
    def __init__(self):
        self.required_docs = {
            'README.md': 'Main project documentation',
            'CHANGELOG.md': 'Version history and changes',
            'LICENSE': 'Project license',
            'CONTRIBUTING.md': 'Contribution guidelines',
            'SECURITY.md': 'Security policy',
            'docs/': 'Documentation directory',
            'docs/README.md': 'Documentation index'
        }
        
        self.code_doc_patterns = {
            'swift': {
                'file_extensions': ['.swift'],
                'doc_comment_pattern': r'^\s*///',
                'function_pattern': r'func\s+\w+',
                'class_pattern': r'class\s+\w+',
                'struct_pattern': r'struct\s+\w+',
                'enum_pattern': r'enum\s+\w+',
                'protocol_pattern': r'protocol\s+\w+'
            }
        }
        
        self.documentation_standards = {
            'min_doc_coverage': 0.7,  # 70% of public APIs should be documented
            'min_readme_sections': 5,
            'required_readme_sections': [
                'installation',
                'usage',
                'api',
                'contributing',
                'license'
            ]
        }
    
    def load_changed_files(self, changed_files_path: str) -> List[str]:
        """Load list of changed files from file"""
        try:
            with open(changed_files_path, 'r') as f:
                return [line.strip() for line in f if line.strip()]
        except FileNotFoundError:
            print(f"Warning: Changed files list '{changed_files_path}' not found")
            return []
    
    def check_required_documentation(self) -> List[str]:
        """Check if all required documentation files exist"""
        issues = []
        
        for doc_path, description in self.required_docs.items():
            if not os.path.exists(doc_path):
                issues.append(f"Missing required documentation: {doc_path} ({description})")
            elif os.path.isdir(doc_path) and not os.listdir(doc_path):
                issues.append(f"Empty documentation directory: {doc_path}")
        
        return issues
    
    def check_readme_quality(self) -> List[str]:
        """Check README.md quality and completeness"""
        issues = []
        
        if not os.path.exists('README.md'):
            issues.append("README.md not found")
            return issues
        
        with open('README.md', 'r', encoding='utf-8') as f:
            content = f.read().lower()
        
        # Check for required sections
        for section in self.documentation_standards['required_readme_sections']:
            if section not in content:
                issues.append(f"README.md missing section: {section}")
        
        # Check minimum length
        if len(content) < 1000:
            issues.append("README.md too short (less than 1000 characters)")
        
        # Check for common issues
        if 'todo' in content or 'fixme' in content:
            issues.append("README.md contains TODO/FIXME items")
        
        return issues
    
    def check_code_documentation(self, changed_files: List[str]) -> List[str]:
        """Check code documentation quality for changed files"""
        issues = []
        
        for file_path in changed_files:
            if not self._is_code_file(file_path):
                continue
            
            file_issues = self._analyze_code_file(file_path)
            issues.extend(file_issues)
        
        return issues
    
    def _is_code_file(self, file_path: str) -> bool:
        """Check if file is a code file that needs documentation"""
        for lang, config in self.code_doc_patterns.items():
            if any(file_path.endswith(ext) for ext in config['file_extensions']):
                return True
        return False
    
    def _analyze_code_file(self, file_path: str) -> List[str]:
        """Analyze a single code file for documentation quality"""
        issues = []
        
        if not os.path.exists(file_path):
            return [f"File not found: {file_path}"]
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except UnicodeDecodeError:
            return [f"Could not read file (encoding issue): {file_path}"]
        
        # Determine file type
        file_type = None
        for lang, config in self.code_doc_patterns.items():
            if any(file_path.endswith(ext) for ext in config['file_extensions']):
                file_type = lang
                break
        
        if not file_type:
            return []
        
        config = self.code_doc_patterns[file_type]
        
        # Find public APIs
        public_apis = []
        for i, line in enumerate(lines):
            for pattern_name in ['function', 'class', 'struct', 'enum', 'protocol']:
                pattern = config[f'{pattern_name}_pattern']
                if re.search(pattern, line) and 'private' not in line and 'internal' not in line:
                    public_apis.append((i, line.strip(), pattern_name))
        
        # Check documentation coverage
        documented_apis = 0
        for api_line_num, api_line, api_type in public_apis:
            # Look for documentation comments before the API
            has_doc = False
            for i in range(max(0, api_line_num - 10), api_line_num):
                if re.match(config['doc_comment_pattern'], lines[i]):
                    has_doc = True
                    break
            
            if has_doc:
                documented_apis += 1
            else:
                issues.append(f"{file_path}:{api_line_num+1}: Undocumented public {api_type}: {api_line[:50]}...")
        
        # Check overall documentation coverage
        if public_apis:
            doc_coverage = documented_apis / len(public_apis)
            if doc_coverage < self.documentation_standards['min_doc_coverage']:
                issues.append(f"{file_path}: Low documentation coverage ({doc_coverage:.1%} < {self.documentation_standards['min_doc_coverage']:.1%})")
        
        return issues
    
    def check_changelog_quality(self) -> List[str]:
        """Check CHANGELOG.md quality"""
        issues = []
        
        if not os.path.exists('CHANGELOG.md'):
            issues.append("CHANGELOG.md not found")
            return issues
        
        with open('CHANGELOG.md', 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for version headers
        if not re.search(r'##\s*\[.*\]', content):
            issues.append("CHANGELOG.md missing version headers")
        
        # Check for recent entries
        if 'unreleased' not in content.lower() and '## [' not in content:
            issues.append("CHANGELOG.md may be outdated (no recent entries)")
        
        return issues
    
    def check_documentation_consistency(self) -> List[str]:
        """Check documentation consistency across files"""
        issues = []
        
        # Check for broken internal links
        doc_files = ['README.md', 'CONTRIBUTING.md', 'SECURITY.md']
        for doc_file in doc_files:
            if os.path.exists(doc_file):
                with open(doc_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                # Look for markdown links
                links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
                for link_text, link_url in links:
                    if link_url.startswith('#'):
                        # Internal anchor link
                        continue
                    elif link_url.startswith('http'):
                        # External link - could validate but skip for now
                        continue
                    elif not os.path.exists(link_url):
                        issues.append(f"{doc_file}: Broken link to '{link_url}'")
        
        return issues
    
    def validate_all(self, changed_files_path: str) -> Dict[str, Any]:
        """Run all documentation validation checks"""
        changed_files = self.load_changed_files(changed_files_path)
        
        all_issues = []
        
        # Check required documentation
        all_issues.extend(self.check_required_documentation())
        
        # Check README quality
        all_issues.extend(self.check_readme_quality())
        
        # Check code documentation for changed files
        all_issues.extend(self.check_code_documentation(changed_files))
        
        # Check changelog quality
        all_issues.extend(self.check_changelog_quality())
        
        # Check documentation consistency
        all_issues.extend(self.check_documentation_consistency())
        
        return {
            'total_issues': len(all_issues),
            'issues': all_issues,
            'changed_files': changed_files,
            'passed': len(all_issues) == 0
        }
    
    def print_report(self, result: Dict[str, Any]):
        """Print documentation validation report"""
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("📚 DOCUMENTATION QUALITY GATE REPORT")
        print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        print("")
        
        if result['changed_files']:
            print(f"📝 Changed files: {len(result['changed_files'])}")
            for file_path in result['changed_files'][:5]:  # Show first 5
                print(f"   - {file_path}")
            if len(result['changed_files']) > 5:
                print(f"   ... and {len(result['changed_files']) - 5} more")
            print("")
        
        if result['total_issues'] == 0:
            print("✅ Documentation quality gate PASSED")
            print("   All documentation checks passed")
        else:
            print(f"❌ Documentation quality gate FAILED")
            print(f"   Found {result['total_issues']} issues:")
            print("")
            
            for i, issue in enumerate(result['issues'], 1):
                print(f"   {i}. {issue}")
        
        print("")

def main():
    parser = argparse.ArgumentParser(description='Validate documentation quality')
    parser.add_argument('changed_files', help='Path to file containing list of changed files')
    
    args = parser.parse_args()
    
    guard = DocumentationGuard()
    result = guard.validate_all(args.changed_files)
    guard.print_report(result)
    
    sys.exit(0 if result['passed'] else 1)

if __name__ == '__main__':
    main()