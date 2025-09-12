#!/usr/bin/env python3
"""
Fix Lean Compilation Errors Script

This script fixes common compilation errors in the cleaned Lean files:
1. Fixes array access syntax (a[i]! -> a.get i)
2. Fixes import issues
3. Fixes other common syntax problems
"""

import os
import re
import subprocess
import shutil
from pathlib import Path
from typing import List, Dict, Tuple

class LeanErrorFixer:
    def __init__(self):
        self.source_dir = Path("benchmarks/vericoding_lean/yaml-depsontop-cleaned")
        self.output_dir = Path("benchmarks/vericoding_lean/yaml-depsontop-fixed")
        self.errors = []
        self.fixed = []
        self.cleaned = []
        
        # Create output directory
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
    def fix_array_access_syntax(self, content: str) -> Tuple[str, List[str]]:
        """Fix array access syntax from a[i]! to a.get i."""
        fixes_applied = []
        
        # Fix: a[i]! -> a.get i
        content = re.sub(r'(\w+)\[(\w+)\]!', r'\1.get \2', content)
        fixes_applied.append("Fixed array access syntax: a[i]! -> a.get i")
        
        # Fix: a[i] -> a.get i (without !)
        content = re.sub(r'(\w+)\[(\w+)\]', r'\1.get \2', content)
        fixes_applied.append("Fixed array access syntax: a[i] -> a.get i")
        
        return content, fixes_applied
    
    def fix_imports(self, content: str) -> Tuple[str, List[str]]:
        """Fix import statements to ensure proper array support."""
        fixes_applied = []
        
        # Add proper imports for array operations
        if 'import Std' in content and 'import Mathlib' in content:
            # Check if we need to add specific array imports
            if 'Array' in content and 'get' in content:
                # Add specific imports for array operations
                content = content.replace(
                    'import Mathlib',
                    'import Mathlib\nimport Mathlib.Data.Array.Basic\nimport Mathlib.Data.Int.Basic'
                )
                fixes_applied.append("Added specific array and int imports")
        
        return content, fixes_applied
    
    def fix_common_syntax_errors(self, content: str) -> Tuple[str, List[str]]:
        """Fix other common syntax errors."""
        fixes_applied = []
        
        # Fix: remove any remaining markdown artifacts
        content = re.sub(r'```lean\s*', '', content)
        content = re.sub(r'\s*```', '', content)
        
        # Fix: ensure proper namespace structure
        if 'namespace DafnyBenchmarks' in content and not content.strip().endswith('end DafnyBenchmarks'):
            content += '\n\nend DafnyBenchmarks'
            fixes_applied.append("Added missing namespace end")
        
        # Fix: remove any remaining backticks
        content = re.sub(r'`{3,}', '', content)
        
        # Fix: ensure proper theorem syntax
        content = re.sub(r'(\w+\.\w+)\s*\(', r'\1 (', content)
        
        return content, fixes_applied
    
    def test_lean_compilation(self, file_path: Path) -> Tuple[bool, List[str]]:
        """Test if a Lean file compiles and return any errors."""
        try:
            # Create a temporary directory for compilation
            temp_dir = Path(f"/tmp/lean_test_{file_path.stem}")
            temp_dir.mkdir(exist_ok=True)
            
            # Copy the file to temp directory
            temp_file = temp_dir / file_path.name
            with open(temp_file, 'w', encoding='utf-8') as f:
                with open(file_path, 'r', encoding='utf-8') as src:
                    f.write(src.read())
            
            # Try to compile with lake
            result = subprocess.run(
                ['lake', 'build'],
                capture_output=True,
                text=True,
                cwd=temp_dir,
                timeout=30
            )
            
            # Clean up temp directory
            shutil.rmtree(temp_dir)
            
            if result.returncode == 0:
                return True, []
            else:
                # Parse error messages
                errors = []
                for line in result.stderr.split('\n'):
                    if 'error:' in line or 'Error:' in line:
                        errors.append(line.strip())
                return False, errors
                
        except subprocess.TimeoutExpired:
            return False, ["Compilation timeout"]
        except Exception as e:
            return False, [f"Compilation error: {e}"]
    
    def process_file(self, file_path: Path) -> bool:
        """Process a single Lean file."""
        print(f"Processing: {file_path.name}")
        
        try:
            # Read the file
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Apply all fixes
            fixes_applied = []
            
            # Fix array access syntax
            content, array_fixes = self.fix_array_access_syntax(content)
            fixes_applied.extend(array_fixes)
            
            # Fix imports
            content, import_fixes = self.fix_imports(content)
            fixes_applied.extend(import_fixes)
            
            # Fix common syntax errors
            content, syntax_fixes = self.fix_common_syntax_errors(content)
            fixes_applied.extend(syntax_fixes)
            
            # Save to output directory
            output_file = self.output_dir / file_path.name
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(content)
            
            # Test compilation
            compiles, errors = self.test_lean_compilation(output_file)
            
            if compiles:
                print(f"  ✓ Fixed and compiles successfully")
                self.cleaned.append(file_path.name)
            else:
                print(f"  ⚠ Fixed but still has compilation errors: {len(errors)} errors")
                self.errors.append({
                    'file': file_path.name,
                    'errors': errors,
                    'fixes_applied': fixes_applied
                })
            
            if fixes_applied:
                print(f"  🔧 Applied fixes: {', '.join(fixes_applied)}")
            
            return True
            
        except Exception as e:
            print(f"  ✗ Error processing file: {e}")
            self.errors.append({
                'file': file_path.name,
                'errors': [f"Processing error: {e}"],
                'fixes_applied': []
            })
            return False
    
    def process_all_files(self):
        """Process all Lean files in the source directory."""
        lean_files = list(self.source_dir.glob("*.lean"))
        total_files = len(lean_files)
        
        print(f"Found {total_files} Lean files to fix")
        print(f"Source: {self.source_dir}")
        print(f"Output: {self.output_dir}")
        print("Starting error fixing...")
        
        processed = 0
        for file_path in lean_files:
            if self.process_file(file_path):
                processed += 1
            print(f"Progress: {processed}/{total_files} ({processed/total_files*100:.1f}%)")
        
        # Print summary
        print(f"\n=== Error Fixing Complete ===")
        print(f"Processed: {processed}/{total_files}")
        print(f"Successfully fixed: {len(self.cleaned)}")
        print(f"Files still with errors: {len(self.errors)}")
        
        if self.errors:
            print(f"\nFiles still with compilation errors:")
            for error_info in self.errors[:10]:  # Show first 10
                print(f"  - {error_info['file']}: {len(error_info['errors'])} errors")
                if error_info['fixes_applied']:
                    print(f"    Applied fixes: {', '.join(error_info['fixes_applied'])}")
            if len(self.errors) > 10:
                print(f"  ... and {len(self.errors) - 10} more files with errors")
        
        # Save error report
        self.save_error_report()
    
    def save_error_report(self):
        """Save a detailed error report."""
        report_file = self.output_dir / "compilation_errors_report.txt"
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write("Lean File Compilation Error Report (After Fixing)\n")
            f.write("=" * 60 + "\n\n")
            
            for error_info in self.errors:
                f.write(f"File: {error_info['file']}\n")
                f.write("-" * 40 + "\n")
                if error_info['fixes_applied']:
                    f.write(f"Fixes applied: {', '.join(error_info['fixes_applied'])}\n")
                f.write("Remaining errors:\n")
                for error in error_info['errors']:
                    f.write(f"  - {error}\n")
                f.write("\n")
        
        print(f"\nDetailed error report saved to: {report_file}")

def main():
    fixer = LeanErrorFixer()
    fixer.process_all_files()

if __name__ == "__main__":
    main()












