#!/usr/bin/env python3
"""
Run a smaller non-Hoare triple experiment with 10 files
"""
import subprocess
import os
import time
import csv
from pathlib import Path

def create_small_temp_dir():
    """Create temp directory with 10 non-Hoare files"""
    temp_dir = Path("temp_non_hoare_small")
    temp_dir.mkdir(exist_ok=True)
    
    # List of 10 non-Hoare files to copy
    files_to_copy = [
        "benchmarks/numpy_specs/sep_thm/NpAdd.lean",
        "benchmarks/numpy_specs/sep_thm/NpSubtract.lean",
        "benchmarks/numpy_specs/sep_thm/NpMultiply.lean",
        "benchmarks/numpy_specs/sep_thm/NpSum.lean",
        "benchmarks/numpy_specs/sep_thm/NpProd.lean",
        "benchmarks/numpy_specs/sep_thm/NpMax.lean",
        "benchmarks/numpy_specs/sep_thm/NpMin.lean",
        "benchmarks/numpy_specs/sep_thm/NpSort.lean",
        "benchmarks/numpy_specs/sep_thm/NpReshape.lean",
        "benchmarks/numpy_specs/sep_thm/NpBroadcast.lean"
    ]
    
    # Copy files
    for file_path in files_to_copy:
        src = Path(file_path)
        if src.exists():
            dst = temp_dir / src.name
            subprocess.run(["cp", str(src), str(dst)], check=True)
            print(f"Copied {src.name}")
    
    return str(temp_dir)

def run_experiment(temp_dir, max_iterations, experiment_name):
    """Run the spec_to_code experiment"""
    print(f"\nStarting {experiment_name} experiment...")
    
    # Create the output directory
    output_dir = f"benchmarks_generated/{experiment_name}"
    os.makedirs(output_dir, exist_ok=True)
    
    # Run the spec_to_code_lean.py script
    start_time = time.time()
    
    cmd = [
        "uv", "run",
        "spec_to_code_lean.py",
        temp_dir,  # Positional argument: folder with .lean files
        "--output-dir", output_dir,
        "--iterations", str(max_iterations)
    ]
    
    try:
        # Run with real-time output
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        
        for line in iter(process.stdout.readline, ''):
            if line:
                print(line, end='')
        
        process.wait()
        
        if process.returncode != 0:
            print(f"Error: Script exited with code {process.returncode}")
    except Exception as e:
        print(f"Error running experiment: {e}")
    
    end_time = time.time()
    print(f"{experiment_name} completed in {end_time - start_time:.2f} seconds")
    
    # Count successes
    results_file = os.path.join(output_dir, "results.csv")
    if os.path.exists(results_file):
        with open(results_file, 'r') as f:
            reader = csv.DictReader(f)
            results = list(reader)
            successes = sum(1 for r in results if r['result'] == 'success')
            print(f"Success count: {successes}/{len(results)}")
            return successes, len(results)
    else:
        print("No results file found")
        return 0, 0

def main():
    print("Running small non-Hoare triple experiment (10 files)...")
    print("=" * 50)
    
    # Create temp directory with 10 files
    temp_dir = create_small_temp_dir()
    
    # Run 1-iteration experiment
    success_1, total_1 = run_experiment(temp_dir, 1, "experiment_non_hoare_small_1iter")
    
    # Run 5-iteration experiment  
    success_5, total_5 = run_experiment(temp_dir, 5, "experiment_non_hoare_small_5iter")
    
    print("\n" + "=" * 50)
    print("Summary:")
    print(f"1-iteration: {success_1}/{total_1} ({100*success_1/total_1 if total_1 > 0 else 0:.1f}%)")
    print(f"5-iteration: {success_5}/{total_5} ({100*success_5/total_5 if total_5 > 0 else 0:.1f}%)")
    print("\nAll experiments completed!")

if __name__ == "__main__":
    main()