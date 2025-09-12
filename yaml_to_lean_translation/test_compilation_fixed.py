#!/usr/bin/env python3
"""
Fixed version of compilation testing script that properly captures error messages from stdout.
Tests each file first without Mathlib import, then with Mathlib if needed.
Generates a CSV report of compilation results.
"""

import os
import subprocess
import csv
import tempfile
import shutil
from pathlib import Path
from typing import Dict, List, Tuple

def test_lean_compilation(file_path: str, temp_dir: str) -> Tuple[bool, str, str]:
    """
    Test compilation of a Lean file using lean -o to create olean files.
    
    Args:
        file_path: Path to the Lean file to test
        temp_dir: Temporary directory for testing
        
    Returns:
        Tuple of (compiles_without_mathlib, compiles_with_mathlib, error_message)
    """
    # Read the original file
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Test 1: Try without Mathlib import
    content_without_mathlib = content.replace('import Mathlib', '-- import Mathlib')
    
    temp_file_path = os.path.join(temp_dir, 'test.lean')
    with open(temp_file_path, 'w') as f:
        f.write(content_without_mathlib)
    
    # Try to compile without Mathlib using lean -o
    result = subprocess.run(
        ['lean', '-o', os.path.join(temp_dir, 'test.olean'), temp_file_path],
        capture_output=True,
        text=True,
        cwd=temp_dir,
        timeout=30
    )
    
    compiles_without_mathlib = result.returncode == 0
    
    # Test 2: Try with Mathlib import (original content)
    with open(temp_file_path, 'w') as f:
        f.write(content)
    
    result_with_mathlib = subprocess.run(
        ['lean', '-o', os.path.join(temp_dir, 'test.olean'), temp_file_path],
        capture_output=True,
        text=True,
        cwd=temp_dir,
        timeout=30
    )
    
    compiles_with_mathlib = result_with_mathlib.returncode == 0
    
    # Get error message if both fail
    error_message = ""
    if not compiles_without_mathlib and not compiles_with_mathlib:
        if result_with_mathlib.stdout:
            error_message = result_with_mathlib.stdout.strip()
        elif result.stdout:
            error_message = result.stdout.strip()
        # If no stdout, try stderr
        if not error_message:
            if result_with_mathlib.stderr:
                error_message = result_with_mathlib.stderr.strip()
            elif result.stderr:
                error_message = result.stderr.strip()
        # Truncate long error messages
        if len(error_message) > 500:
            error_message = error_message[:497] + "..."
    
    return compiles_without_mathlib, compiles_with_mathlib, error_message

def get_compilation_status(compiles_without_mathlib: bool, compiles_with_mathlib: bool) -> str:
    """Convert compilation results to a readable status string."""
    if compiles_without_mathlib:
        return "Compiles without Mathlib"
    elif compiles_with_mathlib:
        return "Compiles with Mathlib"
    else:
        return "Compilation Error"

def main():
    """Main function to test all Lean files and generate CSV report."""
    # Path to the converted files
    converted_dir = "benchmarks/vericoding_lean/yaml-depsontop-converted"
    
    if not os.path.exists(converted_dir):
        print(f"Error: Directory {converted_dir} not found!")
        return
    
    # Get all .lean files
    lean_files = list(Path(converted_dir).glob("*.lean"))
    
    if not lean_files:
        print(f"No .lean files found in {converted_dir}")
        return
    
    print(f"Found {len(lean_files)} Lean files to test")
    
    # Create temporary directory for testing
    with tempfile.TemporaryDirectory() as temp_dir:
        # Test each file
        results = []
        
        for i, lean_file in enumerate(lean_files, 1):
            print(f"Testing {i}/{len(lean_files)}: {lean_file.name}")
            
            try:
                compiles_without_mathlib, compiles_with_mathlib, error_message = test_lean_compilation(
                    str(lean_file), temp_dir
                )
                
                status = get_compilation_status(compiles_without_mathlib, compiles_with_mathlib)
                
                results.append({
                    'filename': lean_file.name,
                    'compiles_without_mathlib': compiles_without_mathlib,
                    'compiles_with_mathlib': compiles_with_mathlib,
                    'status': status,
                    'error_message': error_message
                })
                
            except Exception as e:
                print(f"Error testing {lean_file.name}: {e}")
                results.append({
                    'filename': lean_file.name,
                    'compiles_without_mathlib': False,
                    'compiles_with_mathlib': False,
                    'status': 'Test Error',
                    'error_message': str(e)
                })
        
        # Generate CSV report
        csv_filename = "lean_compilation_report_fixed.csv"
        
        with open(csv_filename, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['filename', 'compiles_without_mathlib', 'compiles_with_mathlib', 'status', 'error_message']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for result in results:
                writer.writerow(result)
        
        # Print summary
        print(f"\nCompilation testing completed!")
        print(f"Results saved to: {csv_filename}")
        
        # Count results
        total = len(results)
        without_mathlib = sum(1 for r in results if r['compiles_without_mathlib'])
        with_mathlib = sum(1 for r in results if r['compiles_with_mathlib'])
        errors = sum(1 for r in results if r['status'] == 'Compilation Error')
        
        print(f"\nSummary:")
        print(f"Total files: {total}")
        print(f"Compile without Mathlib: {without_mathlib}")
        print(f"Compile with Mathlib: {with_mathlib}")
        print(f"Compilation errors: {errors}")

if __name__ == "__main__":
    main()











