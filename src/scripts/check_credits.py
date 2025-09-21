#!/usr/bin/env python3
"""
Check W&B runs for credit status by examining log files for "Insufficient credits" phrase.
"""

import argparse
import wandb
import os
import sys
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Dataset name mapping (from sum_runtime.py)
DATASET_MAPPING = {
    'dafnybench': 'dbench',
    'apps': 'apps', 
    'bignum': 'bignum',
    'humaneval': 'heval',
    'numpy_simple': 'numpy_simple',
    'numpy_triple': 'numpy_triple',
    'verina': 'verina'
}

def extract_dataset(config, debug=False):
    """Extract dataset from config folder."""
    return config.get('files_dir', 'N/A')

def check_insufficient_credits(run):
    """Check if run logs contain 'Insufficient credits' phrase."""
    # Get the log file from the run
    files = run.files()
    
    for file in files:
        if file.name == 'output.log':
            # Download and read the log file
            downloaded_file = file.download(replace=True)
            with open(downloaded_file.name, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            # Clean up the downloaded file immediately
            os.remove(downloaded_file.name)
            
            return "Insufficient credits" in content
    else:
        # No output.log found - crash the script
        raise FileNotFoundError(f"No output.log found for run {run.name}")

def get_runs_credit_status(tags, project="vericoding", entity=None, debug=False):
    """Fetch runs and check their credit status."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    # Handle multiple tags
    if isinstance(tags, str):
        tags = [tags]
    
    # Create filter for any of the specified tags
    tag_filter = {"tags": {"$in": tags}}
    
    runs = api.runs(project_path, filters=tag_filter)
    
    results = []
    
    for i, run in enumerate(runs):
        config = run.config
        
        # Debug: print run structure for first few runs
        if debug and i < 3:
            print(f"\nDEBUG: Run {run.name}", file=sys.stderr)
            print(f"Config keys: {list(config.keys())}", file=sys.stderr)
            print(f"Tags: {run.tags}", file=sys.stderr)
            print("-" * 50, file=sys.stderr)
        
        # Extract model info (check both old and new attribute names)
        model = config.get('llm_provider', '') or config.get('llm', '')
        
        # Extract dataset
        dataset = extract_dataset(config, debug)
        
        # Extract shard
        shard = config.get('shard', 'N/A')
        
        # Check for insufficient credits
        print(f"Checking credits for {run.name}...", file=sys.stderr)
        has_insufficient_credits = check_insufficient_credits(run)
        
        credit_status = "INSUFFICIENT" if has_insufficient_credits else "OK"
        
        results.append({
            'run_name': run.name,
            'model': model,
            'dataset': dataset,
            'shard': shard,
            'credit_status': credit_status,
            'tags': list(run.tags)
        })
    
    return results

def print_credit_report(results):
    """Print a formatted report of credit status."""
    
    if not results:
        print("No runs found for the specified tags.")
        return
    
    print(f"\n=== CREDIT STATUS REPORT ===")
    print(f"Total runs: {len(results)}")
    
    # Count by status
    status_counts = {}
    for result in results:
        status = result['credit_status']
        status_counts[status] = status_counts.get(status, 0) + 1
    
    print(f"Status summary:")
    for status, count in sorted(status_counts.items()):
        print(f"  {status}: {count}")
    
    print(f"\n=== DETAILED BREAKDOWN ===")
    
    # Sort by model, then dataset, then shard
    sorted_results = sorted(results, key=lambda x: (x['model'], x['dataset'], str(x['shard'])))
    
    # Group by credit status for easier reading
    for status in ['INSUFFICIENT', 'OK']:
        status_results = [r for r in sorted_results if r['credit_status'] == status]
        if status_results:
            print(f"\n--- {status} CREDITS ---")
            for result in status_results:
                print(f"{result['model']:<20} | {result['dataset']:<40} | shard:{result['shard']:<5} | {result['run_name']}")

def main():
    parser = argparse.ArgumentParser(description="Check W&B runs for credit status")
    parser.add_argument("tags", nargs='+', help="W&B tags to filter results (can specify multiple)")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    print(f"Checking credit status for tags: {', '.join(args.tags)}", file=sys.stderr)
    results = get_runs_credit_status(args.tags, args.project, args.entity, args.debug)
    
    print_credit_report(results)

if __name__ == "__main__":
    main()
