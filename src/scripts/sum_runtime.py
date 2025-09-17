#!/usr/bin/env python3
"""
Sum the runtime and costs from W&B runs for a specific tag.
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

# Pricing data from batch_experiments.py (USD per million tokens)
MODEL_PRICING = {
    'claude-opus': {'input': 15.0, 'output': 75.0},
    'claude-sonnet': {'input': 3.0, 'output': 15.0},
    'deepseek': {'input': 0.25, 'output': 1.0},
    'gemini': {'input': 1.25, 'output': 10.0},
    'gemini-flash': {'input': 0.30, 'output': 2.50},
    'glm': {'input': 0.413, 'output': 1.65},
    'gpt': {'input': 1.25, 'output': 10.0},
    'gpt-mini': {'input': 0.25, 'output': 2.0},
    'grok': {'input': 3.0, 'output': 15.0},
    'grok-code': {'input': 0.20, 'output': 1.50},
}

# Dataset name mapping
DATASET_MAPPING = {
    'dafnybench': 'dbench',
    'apps': 'apps', 
    'bignum': 'bignum',
    'humaneval': 'heval',
    'numpy_simple': 'numpy_simple',
    'numpy_triple': 'numpy_triple',
    'verina': 'verina'
}

def calculate_cost(llm_provider, input_tokens, output_tokens):
    """Calculate cost based on model pricing and token usage."""
    if llm_provider not in MODEL_PRICING:
        return 0.0
    
    pricing = MODEL_PRICING[llm_provider]
    input_cost = (input_tokens / 1_000_000) * pricing['input']
    output_cost = (output_tokens / 1_000_000) * pricing['output']
    
    return input_cost + output_cost

def get_runtime_data(tag, project="vericoding", entity=None, debug=False):
    """Fetch runtime and cost data from W&B for a specific tag."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    runs = api.runs(project_path, filters={"tags": {"$in": [tag]}})
    
    runtime_data = defaultdict(lambda: defaultdict(dict))
    total_runtime = 0
    total_cost = 0
    total_input_tokens = 0
    total_output_tokens = 0
    
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
            print(f"Input tokens: {run.summary.get('llm/total_input_tokens', 'Not found')}", file=sys.stderr)
            print(f"Output tokens: {run.summary.get('llm/total_output_tokens', 'Not found')}", file=sys.stderr)
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
            
        # Get token usage
        input_tokens = run.summary.get('llm/total_input_tokens', 0) or 0
        output_tokens = run.summary.get('llm/total_output_tokens', 0) or 0
        
        # Calculate cost
        cost = calculate_cost(llm_provider, input_tokens, output_tokens)
        
        # Map model name
        model_name = MODEL_MAPPING.get(llm_provider, llm_provider)
        
        # Store runtime data
        runtime_data[model_name][dataset] = {
            'runtime_seconds': runtime_seconds,
            'runtime_minutes': runtime_seconds / 60.0,
            'runtime_hours': runtime_seconds / 3600.0,
            'input_tokens': input_tokens,
            'output_tokens': output_tokens,
            'cost_usd': cost
        }
        
        total_runtime += runtime_seconds
        total_cost += cost
        total_input_tokens += input_tokens
        total_output_tokens += output_tokens
        
        print(f"Found: {model_name} + {dataset} = {runtime_seconds:.0f}s ({runtime_seconds/60:.1f}m) | {input_tokens:,}+{output_tokens:,} tokens | ${cost:.2f}", file=sys.stderr)
    
    return runtime_data, total_runtime, total_cost, total_input_tokens, total_output_tokens

def format_tokens(tokens):
    """Format token count in scientific notation with 2 significant figures."""
    if tokens >= 1_000_000:
        if tokens >= 10_000_000:
            return f"{tokens/1_000_000:.0f}e6"  # e.g., 49e6 instead of 49.5e6
        else:
            return f"{tokens/1_000_000:.1f}e6"  # e.g., 4.5e6
    elif tokens >= 1_000:
        if tokens >= 10_000:
            return f"{tokens/1_000:.0f}k"  # e.g., 45k instead of 45.1k
        else:
            return f"{tokens/1_000:.1f}k"  # e.g., 4.5k
    else:
        return str(int(tokens))

def print_runtime_summary(runtime_data, total_runtime, total_cost, total_input_tokens, total_output_tokens):
    """Print a summary of runtime and cost data."""
    
    print(f"\n=== OVERALL SUMMARY ===")
    print(f"Total runtime: {total_runtime:.0f} seconds ({total_runtime/60:.1f} minutes, {total_runtime/3600:.1f} hours)")
    print(f"Total cost: ${total_cost:.2f}")
    print(f"Total tokens: {format_tokens(total_input_tokens)} input + {format_tokens(total_output_tokens)} output = {format_tokens(total_input_tokens + total_output_tokens)} total")
    
    # Sum by model
    print(f"\n=== BY MODEL ===")
    model_totals = defaultdict(lambda: {'runtime': 0, 'cost': 0, 'input_tokens': 0, 'output_tokens': 0})
    for model_name, datasets in runtime_data.items():
        for dataset, data in datasets.items():
            model_totals[model_name]['runtime'] += data['runtime_seconds']
            model_totals[model_name]['cost'] += data['cost_usd']
            model_totals[model_name]['input_tokens'] += data['input_tokens']
            model_totals[model_name]['output_tokens'] += data['output_tokens']
    
    for model_name in sorted(model_totals.keys()):
        totals = model_totals[model_name]
        runtime_hours = totals['runtime'] / 3600
        print(f"{model_name}: {runtime_hours:.1f}h | ${totals['cost']:.2f} | {format_tokens(totals['input_tokens'])}+{format_tokens(totals['output_tokens'])} tokens")
    
    # Sum by dataset
    print(f"\n=== BY DATASET ===")
    dataset_totals = defaultdict(lambda: {'runtime': 0, 'cost': 0, 'input_tokens': 0, 'output_tokens': 0})
    for model_name, datasets in runtime_data.items():
        for dataset, data in datasets.items():
            dataset_totals[dataset]['runtime'] += data['runtime_seconds']
            dataset_totals[dataset]['cost'] += data['cost_usd']
            dataset_totals[dataset]['input_tokens'] += data['input_tokens']
            dataset_totals[dataset]['output_tokens'] += data['output_tokens']
    
    for dataset in sorted(dataset_totals.keys()):
        totals = dataset_totals[dataset]
        runtime_hours = totals['runtime'] / 3600
        print(f"{dataset}: {runtime_hours:.1f}h | ${totals['cost']:.2f} | {format_tokens(totals['input_tokens'])}+{format_tokens(totals['output_tokens'])} tokens")
    
    # Detailed breakdown
    print(f"\n=== DETAILED BREAKDOWN ===")
    for model_name in sorted(runtime_data.keys()):
        print(f"\n{model_name}:")
        for dataset in sorted(runtime_data[model_name].keys()):
            data = runtime_data[model_name][dataset]
            print(f"  {dataset}: {data['runtime_minutes']:.1f}m | ${data['cost_usd']:.2f} | {format_tokens(data['input_tokens'])}+{format_tokens(data['output_tokens'])} tokens")

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
    
    print(f"Fetching runtime and cost data for tag: {args.tag}", file=sys.stderr)
    runtime_data, total_runtime, total_cost, total_input_tokens, total_output_tokens = get_runtime_data(args.tag, args.project, args.entity, args.debug)
    
    if not runtime_data:
        print("No runtime data found for the specified tag", file=sys.stderr)
        return
    
    print_runtime_summary(runtime_data, total_runtime, total_cost, total_input_tokens, total_output_tokens)

if __name__ == "__main__":
    main()
