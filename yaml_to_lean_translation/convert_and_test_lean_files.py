#!/usr/bin/env python3
"""
Convert and Test Lean Files Script

This script:
1. Converts a.get i syntax back to a[i]! syntax in all cleaned Lean files
2. Tests compilation of each file
3. Generates a CSV report showing which files compiled successfully vs failed
"""

import os
import re
import subprocess
import shutil
import csv
from pathlib import Path
from typing import List, Dict, Tuple

class LeanSyntaxConverter:
    def __init__(self):
        self.source_dir = Path("benchmarks/vericoding_lean/yaml-depsontop-cleaned")
        self.output_dir = Path("benchmarks/vericoding_lean/yaml-depsontop-converted")
        self.results = []
        
        # Create output directory
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
    def convert_syntax(self, content: str) -> str:
        """Convert a.get i syntax back to a[i]! syntax."""
        # Convert a.get i -> a[i]!
        content = re.sub(r'(\w+)\.get\s+(\w+)', r'\1[\2]!', content)
        return content
    
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
    
    def process_file(self, file_path: Path) -> Dict:
        """Process a single Lean file."""
        print(f"Processing: {file_path.name}")
        
        try:
            # Read the file
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Convert syntax
            converted_content = self.convert_syntax(content)
            
            # Save converted file
            output_file = self.output_dir / file_path.name
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(converted_content)
            
            # Test compilation
            compiles, errors = self.test_lean_compilation(output_file)
            
            # Record results
            result = {
                'filename': file_path.name,
                'compiles': compiles,
                'error_count': len(errors),
                'errors': '; '.join(errors) if errors else '',
                'syntax_converted': 'a.get i -> a[i]!' if 'a.get' in content else 'No conversion needed'
            }
            
            if compiles:
                print(f"  ✓ Converted and compiles successfully")
            else:
                print(f"  ⚠ Converted but has compilation errors: {len(errors)} errors")
            
            return result
            
        except Exception as e:
            print(f"  ✗ Error processing file: {e}")
            return {
                'filename': file_path.name,
                'compiles': False,
                'error_count': 1,
                'errors': f"Processing error: {e}",
                'syntax_converted': 'Error during processing'
            }
    
    def process_all_files(self):
        """Process all Lean files in the source directory."""
        lean_files = list(self.source_dir.glob("*.lean"))
        total_files = len(lean_files)
        
        print(f"Found {total_files} Lean files to convert and test")
        print(f"Source: {self.source_dir}")
        print(f"Output: {self.output_dir}")
        print("Starting syntax conversion and compilation testing...")
        
        processed = 0
        for file_path in lean_files:
            result = self.process_file(file_path)
            self.results.append(result)
            processed += 1
            print(f"Progress: {processed}/{total_files} ({processed/total_files*100:.1f}%)")
        
        # Print summary
        print(f"\n=== Conversion and Testing Complete ===")
        print(f"Processed: {processed}/{total_files}")
        
        successful = sum(1 for r in self.results if r['compiles'])
        failed = sum(1 for r in self.results if not r['compiles'])
        
        print(f"Successfully compiled: {successful}")
        print(f"Failed to compile: {failed}")
        
        # Generate CSV report
        self.generate_csv_report()
    
    def generate_csv_report(self):
        """Generate a CSV report of compilation results."""
        csv_file = self.output_dir / "compilation_results.csv"
        
        with open(csv_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['filename', 'compiles', 'error_count', 'errors', 'syntax_converted']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for result in self.results:
                writer.writerow(result)
        
        print(f"\nCSV report saved to: {csv_file}")
        
        # Also generate a summary report
        summary_file = self.output_dir / "compilation_summary.txt"
        with open(summary_file, 'w', encoding='utf-8') as f:
            f.write("Lean File Compilation Summary Report\n")
            f.write("=" * 50 + "\n\n")
            
            f.write(f"Total files processed: {len(self.results)}\n")
            f.write(f"Successfully compiled: {successful}\n")
            f.write(f"Failed to compile: {failed}\n")
            f.write(f"Success rate: {successful/len(self.results)*100:.1f}%\n\n")
            
            if failed > 0:
                f.write("Files that failed to compile:\n")
                f.write("-" * 40 + "\n")
                for result in self.results:
                    if not result['compiles']:
                        f.write(f"- {result['filename']}: {result['errors']}\n")
        
        print(f"Summary report saved to: {summary_file}")

def main():
    converter = LeanSyntaxConverter()
    converter.process_all_files()

if __name__ == "__main__":
    main()












