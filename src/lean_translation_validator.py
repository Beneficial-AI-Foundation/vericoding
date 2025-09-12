#!/usr/bin/env python3
"""
Lean Translation Quality Validator

This script validates Lean 4 translations of Dafny specifications to ensure
they preserve the core meaning and meet quality standards.
"""

import os
import sys
import json
import argparse
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
import re

@dataclass
class ValidationResult:
    """Result of validation checks"""
    filename: str
    syntax_valid: bool
    imports_valid: bool
    hoare_triple_present: bool
    sorry_present: bool
    has_comments: bool
    type_annotations: bool
    overall_score: float
    issues: List[str]
    suggestions: List[str]

class LeanTranslationValidator:
    """Validates Lean 4 translations for quality and correctness"""
    
    def __init__(self, lean_path: str = "lean"):
        self.lean_path = lean_path
        
    def check_syntax(self, lean_file: Path) -> Tuple[bool, List[str]]:
        """Check if Lean file has valid syntax"""
        try:
            result = subprocess.run(
                [self.lean_path, str(lean_file)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                return True, []
            else:
                return False, [result.stderr]
                
        except subprocess.TimeoutExpired:
            return False, ["Syntax check timed out"]
        except Exception as e:
            return False, [f"Syntax check failed: {e}"]
    
    def check_imports(self, content: str) -> Tuple[bool, List[str]]:
        """Check if necessary imports are present"""
        required_imports = [
            "Std.Do.Triple",
            "Std.Tactic.Do"
        ]
        
        missing_imports = []
        for imp in required_imports:
            if imp not in content:
                missing_imports.append(imp)
        
        return len(missing_imports) == 0, missing_imports
    
    def check_hoare_triple(self, content: str) -> Tuple[bool, List[str]]:
        """Check if Hoare triple specification is present"""
        # Look for Hoare triple pattern
        hoare_pattern = r'⦃⌜.*⌝⦄.*⦃⇓.*=>.*⌝⦄'
        if re.search(hoare_pattern, content, re.DOTALL):
            return True, []
        else:
            return False, ["No Hoare triple specification found"]
    
    def check_sorry_present(self, content: str) -> Tuple[bool, List[str]]:
        """Check if 'sorry' is present (indicating incomplete proof)"""
        if "sorry" in content:
            return True, []
        else:
            return False, ["No 'sorry' found - proof might be incomplete"]
    
    def check_comments(self, content: str) -> Tuple[bool, List[str]]:
        """Check if file has helpful comments"""
        comment_lines = len([line for line in content.split('\n') 
                           if line.strip().startswith('/--') or line.strip().startswith('--')])
        total_lines = len(content.split('\n'))
        
        comment_ratio = comment_lines / total_lines if total_lines > 0 else 0
        
        if comment_ratio >= 0.1:  # At least 10% comments
            return True, []
        else:
            return False, [f"Low comment ratio: {comment_ratio:.2%}"]
    
    def check_type_annotations(self, content: str) -> Tuple[bool, List[str]]:
        """Check if functions have type annotations"""
        # Look for function definitions with type annotations
        function_pattern = r'def\s+\w+\s*\([^)]*\)\s*:'
        if re.search(function_pattern, content):
            return True, []
        else:
            return False, ["Function definitions missing type annotations"]
    
    def analyze_translation_quality(self, content: str, original_dafny: str = "") -> Dict[str, any]:
        """Analyze the overall quality of the translation"""
        quality_metrics = {}
        
        # Check for common translation patterns
        patterns = {
            'array_operations': r'Array\s+\w+',
            'fin_usage': r'Fin\s+\w+',
            'existential_quant': r'∃\s+\w+',
            'universal_quant': r'∀\s+\w+',
            'option_usage': r'Option\s+\w+',
            'list_operations': r'List\s+\w+',
            'hashmap_usage': r'Std\.HashMap',
            'hashset_usage': r'Std\.HashSet'
        }
        
        for pattern_name, pattern in patterns.items():
            quality_metrics[pattern_name] = bool(re.search(pattern, content))
        
        # Check for proper Lean idioms
        idioms = {
            'do_notation': 'do' in content,
            'match_expression': 'match' in content,
            'let_expressions': 'let' in content,
            'theorem_declarations': 'theorem' in content,
            'lemma_declarations': 'lemma' in content
        }
        
        quality_metrics.update(idioms)
        
        return quality_metrics
    
    def validate_file(self, lean_file: Path, original_dafny: str = "") -> ValidationResult:
        """Validate a single Lean translation file"""
        
        try:
            with open(lean_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return ValidationResult(
                filename=lean_file.name,
                syntax_valid=False,
                imports_valid=False,
                hoare_triple_present=False,
                sorry_present=False,
                has_comments=False,
                type_annotations=False,
                overall_score=0.0,
                issues=[f"Failed to read file: {e}"],
                suggestions=[]
            )
        
        # Run all checks
        syntax_valid, syntax_issues = self.check_syntax(lean_file)
        imports_valid, import_issues = self.check_imports(content)
        hoare_present, hoare_issues = self.check_hoare_triple(content)
        sorry_present, sorry_issues = self.check_sorry_present(content)
        has_comments, comment_issues = self.check_comments(content)
        has_types, type_issues = self.check_type_annotations(content)
        
        # Collect all issues
        all_issues = (syntax_issues + import_issues + hoare_issues + 
                     sorry_issues + comment_issues + type_issues)
        
        # Calculate overall score
        checks = [
            syntax_valid,
            imports_valid,
            hoare_present,
            sorry_present,
            has_comments,
            has_types
        ]
        
        overall_score = sum(checks) / len(checks)
        
        # Generate suggestions
        suggestions = []
        if not syntax_valid:
            suggestions.append("Fix syntax errors in Lean code")
        if not imports_valid:
            suggestions.append("Add missing imports: " + ", ".join(import_issues))
        if not hoare_present:
            suggestions.append("Add Hoare triple specification")
        if not sorry_present:
            suggestions.append("Add 'sorry' for incomplete proofs")
        if not has_comments:
            suggestions.append("Add more comments explaining the translation")
        if not has_types:
            suggestions.append("Add type annotations to function definitions")
        
        # Analyze quality patterns
        quality_metrics = self.analyze_translation_quality(content, original_dafny)
        
        # Add quality-based suggestions
        if not quality_metrics.get('fin_usage', False):
            suggestions.append("Consider using Fin for bounded indices")
        if not quality_metrics.get('option_usage', False):
            suggestions.append("Consider using Option for nullable values")
        
        return ValidationResult(
            filename=lean_file.name,
            syntax_valid=syntax_valid,
            imports_valid=imports_valid,
            hoare_triple_present=hoare_present,
            sorry_present=sorry_present,
            has_comments=has_comments,
            type_annotations=has_types,
            overall_score=overall_score,
            issues=all_issues,
            suggestions=suggestions
        )
    
    def validate_directory(self, lean_dir: Path) -> List[ValidationResult]:
        """Validate all Lean files in a directory"""
        results = []
        
        for lean_file in lean_dir.glob("*.lean"):
            result = self.validate_file(lean_file)
            results.append(result)
        
        return results
    
    def generate_report(self, results: List[ValidationResult], output_file: Path):
        """Generate a comprehensive validation report"""
        
        # Calculate statistics
        total_files = len(results)
        syntax_valid = sum(1 for r in results if r.syntax_valid)
        imports_valid = sum(1 for r in results if r.imports_valid)
        hoare_present = sum(1 for r in results if r.hoare_triple_present)
        sorry_present = sum(1 for r in results if r.sorry_present)
        has_comments = sum(1 for r in results if r.has_comments)
        has_types = sum(1 for r in results if r.type_annotations)
        
        avg_score = sum(r.overall_score for r in results) / total_files if total_files > 0 else 0
        
        # Generate report
        report = {
            'summary': {
                'total_files': total_files,
                'syntax_valid': syntax_valid,
                'imports_valid': imports_valid,
                'hoare_triple_present': hoare_present,
                'sorry_present': sorry_present,
                'has_comments': has_comments,
                'type_annotations': has_types,
                'average_score': avg_score,
                'success_rate': syntax_valid / total_files * 100 if total_files > 0 else 0
            },
            'files': [
                {
                    'filename': r.filename,
                    'syntax_valid': r.syntax_valid,
                    'imports_valid': r.imports_valid,
                    'hoare_triple_present': r.hoare_triple_present,
                    'sorry_present': r.sorry_present,
                    'has_comments': r.has_comments,
                    'type_annotations': r.type_annotations,
                    'overall_score': r.overall_score,
                    'issues': r.issues,
                    'suggestions': r.suggestions
                }
                for r in results
            ],
            'recommendations': {
                'high_priority': [
                    "Fix syntax errors in files with invalid syntax",
                    "Add missing imports to files without required imports",
                    "Add Hoare triple specifications where missing"
                ],
                'medium_priority': [
                    "Add type annotations to function definitions",
                    "Add 'sorry' for incomplete proofs",
                    "Improve comment coverage"
                ],
                'low_priority': [
                    "Consider using Lean 4 idioms like Fin and Option",
                    "Add more detailed translation comments"
                ]
            }
        }
        
        # Save report
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        return report

def main():
    parser = argparse.ArgumentParser(
        description="Validate Lean 4 translations for quality and correctness",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python lean_translation_validator.py ./lean_translations
  python lean_translation_validator.py ./lean_translations --output report.json
  python lean_translation_validator.py ./lean_translations --single-file example.lean
        """
    )
    
    parser.add_argument(
        'lean_dir',
        type=str,
        help='Directory containing Lean translation files'
    )
    
    parser.add_argument(
        '--output',
        type=str,
        default='validation_report.json',
        help='Output file for validation report (default: validation_report.json)'
    )
    
    parser.add_argument(
        '--single-file',
        type=str,
        help='Validate only a single file (relative to lean_dir)'
    )
    
    parser.add_argument(
        '--lean-path',
        type=str,
        default='lean',
        help='Path to Lean executable (default: lean)'
    )
    
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Show detailed validation results'
    )
    
    args = parser.parse_args()
    
    # Setup paths
    lean_path = Path(args.lean_dir)
    output_path = Path(args.output)
    
    if not lean_path.exists():
        print(f"Error: Lean directory {lean_path} does not exist")
        sys.exit(1)
    
    # Initialize validator
    validator = LeanTranslationValidator(args.lean_path)
    
    # Validate files
    if args.single_file:
        lean_file = lean_path / args.single_file
        if not lean_file.exists():
            print(f"Error: File {lean_file} does not exist")
            sys.exit(1)
        results = [validator.validate_file(lean_file)]
    else:
        results = validator.validate_directory(lean_path)
    
    if not results:
        print(f"No .lean files found in {lean_path}")
        sys.exit(1)
    
    print(f"Validating {len(results)} Lean files...")
    
    # Show results
    for result in results:
        status = "✅" if result.overall_score >= 0.8 else "⚠️" if result.overall_score >= 0.5 else "❌"
        print(f"{status} {result.filename}: {result.overall_score:.2f}")
        
        if args.verbose and result.issues:
            for issue in result.issues:
                print(f"  - {issue}")
    
    # Generate report
    report = validator.generate_report(results, output_path)
    
    # Print summary
    summary = report['summary']
    print(f"\n{'='*50}")
    print(f"Validation Summary:")
    print(f"  Total files: {summary['total_files']}")
    print(f"  Syntax valid: {summary['syntax_valid']}/{summary['total_files']}")
    print(f"  Imports valid: {summary['imports_valid']}/{summary['total_files']}")
    print(f"  Hoare triples: {summary['hoare_triple_present']}/{summary['total_files']}")
    print(f"  Has 'sorry': {summary['sorry_present']}/{summary['total_files']}")
    print(f"  Has comments: {summary['has_comments']}/{summary['total_files']}")
    print(f"  Type annotations: {summary['type_annotations']}/{summary['total_files']}")
    print(f"  Average score: {summary['average_score']:.2f}")
    print(f"  Success rate: {summary['success_rate']:.1f}%")
    
    print(f"\nDetailed report saved to: {output_path}")

if __name__ == "__main__":
    main()
