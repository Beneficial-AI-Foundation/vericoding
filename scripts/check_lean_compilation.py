#!/usr/bin/env python3

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Any
import time

def run_lean_check(lean_file: Path) -> Dict[str, Any]:
    """Run lean on a single file and return compilation result.
    
    Args:
        lean_file: Path to the Lean file to check
        
    Returns:
        Dictionary with file info and compilation result
    """
    result = {
        "file": str(lean_file),
        "success": False,
        "error": None,
        "exit_code": None
    }
    
    try:
        # Run lean on the file - it will check compilation and exit with non-zero on errors
        cmd = ["lean", str(lean_file)]
        
        # Run the command and capture output
        process = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30  # 30 second timeout per file
        )
        
        result["exit_code"] = process.returncode
        result["success"] = process.returncode == 0
        
        if not result["success"]:
            # Capture both stdout and stderr for compilation errors
            error_output = []
            if process.stdout.strip():
                error_output.append(process.stdout.strip())
            if process.stderr.strip():
                error_output.append(process.stderr.strip())
            result["error"] = "\n".join(error_output) if error_output else "Unknown error"
            
    except subprocess.TimeoutExpired:
        result["error"] = "Compilation timeout (30s)"
        result["exit_code"] = -1
    except Exception as e:
        result["error"] = f"Failed to run lean: {str(e)}"
        result["exit_code"] = -1
    
    return result

def check_lean_files(no_units_dir: Path, output_file: Path) -> None:
    """Check all Lean files in no_units directory and log failures.
    
    Args:
        no_units_dir: Path to the no_units directory containing Lean files
        output_file: Path to output JSON file for logging failures
    """
    if not no_units_dir.exists():
        print(f"Error: Directory {no_units_dir} does not exist")
        return
    
    if not no_units_dir.is_dir():
        print(f"Error: {no_units_dir} is not a directory")
        return
    
    # Find all .lean files in the directory
    lean_files = sorted(list(no_units_dir.glob("*.lean")))
    
    if not lean_files:
        print(f"No .lean files found in {no_units_dir}")
        return
    
    print(f"Found {len(lean_files)} Lean files to check...")
    
    # Results storage
    all_results = []
    failed_files = []
    successful_files = []
    
    # Process each file
    for i, lean_file in enumerate(lean_files, 1):
        print(f"Checking {i}/{len(lean_files)}: {lean_file.name}", end=" ... ")
        
        result = run_lean_check(lean_file)
        all_results.append(result)
        
        if result["success"]:
            print("✓")
            successful_files.append(str(lean_file))
        else:
            print("✗")
            failed_files.append(str(lean_file))
    
    # Create summary
    summary = {
        "total_files": len(lean_files),
        "successful": len(successful_files),
        "failed": len(failed_files),
        "success_rate": len(successful_files) / len(lean_files) if lean_files else 0,
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")
    }
    
    # Create output data
    output_data = {
        "summary": summary,
        "failed_files": failed_files,
        "successful_files": successful_files,
        "detailed_results": all_results
    }
    
    # Write results to JSON file
    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)
    
    # Print summary
    print(f"\n=== Compilation Summary ===")
    print(f"Total files: {summary['total_files']}")
    print(f"Successful: {summary['successful']}")
    print(f"Failed: {summary['failed']}")
    print(f"Success rate: {summary['success_rate']:.1%}")
    print(f"Results saved to: {output_file}")
    
    # Print first few failures for quick reference
    if failed_files:
        print(f"\nFirst 10 failed files:")
        for failed_file in failed_files[:10]:
            print(f"  - {Path(failed_file).name}")
        if len(failed_files) > 10:
            print(f"  ... and {len(failed_files) - 10} more")

def main():
    parser = argparse.ArgumentParser(description='Check Lean compilation for files in no_units directory')
    parser.add_argument('--no-units-dir', type=Path, 
                       default=Path('benchmarks/lean/fvapps/files/no_units'),
                       help='Path to no_units directory containing Lean files')
    parser.add_argument('--output', type=Path,
                       default=Path('benchmarks/lean/fvapps/files/compilation_failures.json'),
                       help='Output JSON file for logging failures')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Show detailed error messages for failed files')
    
    args = parser.parse_args()
    
    # Check if lean is available
    try:
        subprocess.run(["lean", "--version"], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("Error: 'lean' command not found. Please ensure Lean is installed and in PATH.")
        sys.exit(1)
    
    # Run the compilation check
    check_lean_files(args.no_units_dir, args.output)
    
    if args.verbose and args.output.exists():
        # Load and display detailed error messages
        with open(args.output, 'r') as f:
            data = json.load(f)
        
        print(f"\n=== Detailed Error Messages ===")
        for result in data["detailed_results"]:
            if not result["success"] and result["error"]:
                print(f"\n{Path(result['file']).name}:")
                print(f"  {result['error']}")

if __name__ == '__main__':
    main()
