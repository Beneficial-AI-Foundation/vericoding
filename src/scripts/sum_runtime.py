#!/usr/bin/env python3
"""
Sum the runtime from W&B runs for a specific tag.
"""

import argparse
import wandb
import os
import sys
from collections import defaultdict
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Model name mapping from W&B provider names to display names
MODEL_MAPPING = {
    'claude-opus': 'claude-opus-4.1',
    'claude-sonnet': 'claude-sonnet-4', 
    'deepseek': 'deepseek-chat-v3.1',
    'gemini': 'gemini-2.5-pro',
    'gemini-flash': 'gemini-2.5-flash',
    'glm': 'glm-4.5',
    'gpt': 'gpt-5',
    'gpt-mini': 'gpt-5-mini',
    'grok': 'grok-4',
    'grok-code': 'grok-code'
}

# Dataset name mapping
DATASET_MAPPING = {
    'dafnybench': 'dbench',
    'apps': 'apps', 
    'bignum': 'bignum',
    'humaneval': 'heval',
    'numpy_simple': 'numpy', 
    'verina': 'verina'
}

def get_runtime_data(tag, project="vericoding", entity=None, debug=False):
    """Fetch runtime data from W&B for a specific tag."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    runs = api.runs(project_path, filters={"tags": {"$in": [tag]}})
    
    runtime_data = defaultdict(lambda: defaultdict(dict))
    total_runtime = 0
    
    for i, run in enumerate(runs):
        # Get model and dataset info
        config = run.config
        summary = run.summary
        
        # Debug: print first few run structures
        if debug and i < 3:
            print(f"\nDEBUG: Run {run.name}", file=sys.stderr)
            print(f"Config keys: {list(config.keys())}", file=sys.stderr)
            print(f"Summary keys: {list(summary.keys())}", file=sys.stderr)
            print(f"Run duration: {run.summary.get('_runtime', 'Not found')}", file=sys.stderr)
            print("-" * 50, file=sys.stderr)
        
        llm_provider = config.get('llm_provider', '')
        language = config.get('language', '')
        
        # Skip non-Lean runs
        if language != 'lean':
            continue
            
        # Try multiple ways to extract dataset
        folder = config.get('folder', '')
        files_dir = config.get('files_dir', '')
        dataset_path = config.get('dataset_path', '')
        spec_folder = config.get('spec_folder', '')
        
        # Combine all possible paths
        all_paths = f"{folder} {files_dir} {dataset_path} {spec_folder}".strip()
        
        dataset = None
        
        # Extract dataset name from any available path
        for ds_key, ds_name in DATASET_MAPPING.items():
            if ds_key in all_paths:
                dataset = ds_name
                break
        
        if not dataset:
            if debug:
                print(f"Warning: Could not determine dataset for run {run.name}", file=sys.stderr)
            continue
            
        # Get runtime in seconds
        runtime_seconds = run.summary.get('_runtime', 0)
        if runtime_seconds is None:
            runtime_seconds = 0
            
        # Map model name
        model_name = MODEL_MAPPING.get(llm_provider, llm_provider)
        
        # Store runtime data
        runtime_data[model_name][dataset] = {
            'runtime_seconds': runtime_seconds,
            'runtime_minutes': runtime_seconds / 60.0,
            'runtime_hours': runtime_seconds / 3600.0
        }
        
        total_runtime += runtime_seconds
        
        print(f"Found: {model_name} + {dataset} = {runtime_seconds:.0f}s ({runtime_seconds/60:.1f}m)", file=sys.stderr)
    
    return runtime_data, total_runtime

def print_runtime_summary(runtime_data, total_runtime):
    """Print a summary of runtime data."""
    
    print(f"\n=== RUNTIME SUMMARY ===")
    print(f"Total runtime across all runs: {total_runtime:.0f} seconds ({total_runtime/60:.1f} minutes, {total_runtime/3600:.1f} hours)")
    
    # Sum by model
    print(f"\n=== BY MODEL ===")
    model_totals = defaultdict(float)
    for model_name, datasets in runtime_data.items():
        for dataset, data in datasets.items():
            model_totals[model_name] += data['runtime_seconds']
    
    for model_name in sorted(model_totals.keys()):
        total_seconds = model_totals[model_name]
        print(f"{model_name}: {total_seconds:.0f}s ({total_seconds/60:.1f}m, {total_seconds/3600:.1f}h)")
    
    # Sum by dataset
    print(f"\n=== BY DATASET ===")
    dataset_totals = defaultdict(float)
    for model_name, datasets in runtime_data.items():
        for dataset, data in datasets.items():
            dataset_totals[dataset] += data['runtime_seconds']
    
    for dataset in sorted(dataset_totals.keys()):
        total_seconds = dataset_totals[dataset]
        print(f"{dataset}: {total_seconds:.0f}s ({total_seconds/60:.1f}m, {total_seconds/3600:.1f}h)")
    
    # Detailed breakdown
    print(f"\n=== DETAILED BREAKDOWN ===")
    for model_name in sorted(runtime_data.keys()):
        print(f"\n{model_name}:")
        for dataset in sorted(runtime_data[model_name].keys()):
            data = runtime_data[model_name][dataset]
            print(f"  {dataset}: {data['runtime_seconds']:.0f}s ({data['runtime_minutes']:.1f}m)")

def main():
    parser = argparse.ArgumentParser(description="Sum runtime from W&B results")
    parser.add_argument("--tag", required=True, help="W&B tag to filter results")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    print(f"Fetching runtime data for tag: {args.tag}", file=sys.stderr)
    runtime_data, total_runtime = get_runtime_data(args.tag, args.project, args.entity, args.debug)
    
    if not runtime_data:
        print("No runtime data found for the specified tag", file=sys.stderr)
        return
    
    print_runtime_summary(runtime_data, total_runtime)

if __name__ == "__main__":
    main()