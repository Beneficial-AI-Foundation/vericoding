#!/usr/bin/env python3
"""
Script to check Lean file compilation and organize them into compiling/non_compiling directories.
"""

import os
import subprocess
import shutil
from pathlib import Path
import sys

def run_lake_build(file_path, cwd=Path.cwd()):
    """Run lake build on a specific file and return the result."""
    try:
        # Run lake build on the specific file
        result = subprocess.run(
            ['lake', 'build', str(file_path)],
            capture_output=True,
            text=True,
            cwd=cwd
        )

        # If lake build fails, try fallback with lake env lean
        if result.returncode != 0:
            print(f"    Lake build failed, trying fallback with lake env lean...")
            fallback_result = subprocess.run(
                ['lake', 'env', 'lean', str(file_path)],
                capture_output=True,
                text=True,
                cwd=cwd
            )
            if fallback_result.returncode == 0:
                return fallback_result.returncode, fallback_result.stdout, fallback_result.stderr

        return result.returncode, result.stdout, result.stderr
    except Exception as e:
        return -1, "", str(e)

def has_only_sorry_warnings(stderr):
    """Check if stderr contains only warnings about sorry's."""
    if not stderr:
        return True
    
    lines = stderr.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        # Check if it's a sorry warning
        if 'sorry' in line.lower() and ('warning' in line.lower() or 'info' in line.lower()):
            continue
        # If it's not a sorry warning and not empty, it's a real error
        return False
    
    return True

def main():
    unformatted_dir = Path('benchmarks/lean/dafnybench/poor/unformatted')
    compiling_dir = Path('benchmarks/lean/dafnybench/poor/compiling')
    non_compiling_dir = Path('benchmarks/lean/dafnybench/poor/non_compiling')
    
    # Ensure directories exist
    compiling_dir.mkdir(exist_ok=True)
    non_compiling_dir.mkdir(exist_ok=True)
    
    if not unformatted_dir.exists():
        print(f"Error: {unformatted_dir} does not exist")
        sys.exit(1)
    
    # Get all .lean files
    lean_files = list(unformatted_dir.glob('*.lean'))
    
    if not lean_files:
        print("No .lean files found in unformatted directory")
        return
    
    print(f"Found {len(lean_files)} .lean files to check")
    
    compiling_count = 0
    non_compiling_count = 0
    
    for lean_file in lean_files:
        print(f"Checking {lean_file.name}...")
        
        # Run lake build
        returncode, stdout, stderr = run_lake_build(lean_file)
        
        # Determine if it compiles successfully (only sorry warnings allowed)
        if returncode == 0 and has_only_sorry_warnings(stderr):
            # Move to compiling directory
            dest_path = compiling_dir / lean_file.name
            shutil.move(str(lean_file), str(dest_path))
            print(f"  ✓ Compiles (moved to compiling/)")
            compiling_count += 1
        else:
            # Move to non_compiling directory
            dest_path = non_compiling_dir / lean_file.name
            shutil.move(str(lean_file), str(dest_path))
            print(f"  ✗ Does not compile (moved to non_compiling/)")
            if stderr:
                print(f"    Error: {stderr[:200]}...")
            non_compiling_count += 1
    
    print(f"\nSummary:")
    print(f"  Compiling files: {compiling_count}")
    print(f"  Non-compiling files: {non_compiling_count}")
    print(f"  Total processed: {compiling_count + non_compiling_count}")

if __name__ == "__main__":
    main()
