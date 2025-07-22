#!/usr/bin/env python3
"""
Run non-Hoare triple experiments with both 1 and 5 iterations
"""
import subprocess
import sys
import os
import time
import csv

def run_experiment(max_iterations, experiment_name):
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
        "-b", "benchmarks",
        "-o", output_dir,
        "-n", str(max_iterations),
        "-c",
        "-l", "non_hoare_specs.txt"
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
    else:
        print("No results file found")

def main():
    print("Running non-Hoare triple experiments...")
    print("=" * 40)
    
    # Run 1-iteration experiment
    run_experiment(1, "experiment_non_hoare_1iter")
    
    # Run 5-iteration experiment  
    run_experiment(5, "experiment_non_hoare_5iter")
    
    print("\nAll experiments completed!")

if __name__ == "__main__":
    main()