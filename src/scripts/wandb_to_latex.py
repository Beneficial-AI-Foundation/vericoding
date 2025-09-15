#!/usr/bin/env python3
"""
Extract W&B results for a specific tag and generate LaTeX table for vericoding paper.
"""

import argparse
import wandb
import os
from collections import defaultdict
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Model name mapping from W&B provider names to LaTeX display names
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
    'numpy_triple': 'numpy', 
    'verina': 'verina'
}

# Column order for the table
COLUMN_ORDER = ['numpy', 'dbench', 'heval', 'verina', 'bignum', 'proofsynth', 'apps']

def get_wandb_results(tag, project="vericoding", entity=None, debug=False):
    """Fetch results from W&B for a specific tag."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    runs = api.runs(project_path, filters={"tags": {"$in": [tag]}})
    
    results = defaultdict(lambda: defaultdict(dict))
    dataset_file_counts = {}  # Track file counts per dataset
    
    for i, run in enumerate(runs):
        # Get model and dataset info
        config = run.config
        summary = run.summary
        
        # Debug: print first few run structures
        if debug and i < 3:
            print(f"\nDEBUG: Run {run.name}")
            print(f"Config keys: {list(config.keys())}")
            print(f"Summary keys: {list(summary.keys())}")
            print(f"Config: {dict(config)}")
            print(f"Summary: {dict(summary)}")
            print("-" * 50)
        
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
                print(f"Warning: Could not determine dataset for run {run.name}")
                print(f"  folder: '{folder}'")
                print(f"  files_dir: '{files_dir}'")
                print(f"  dataset_path: '{dataset_path}'")
                print(f"  spec_folder: '{spec_folder}'")
            continue
            
        # Get success percentage - raise error if not found
        if 'results/success_rate_percent' not in summary:
            raise ValueError(f"Could not find success rate in W&B summary for run {run.name}. Available keys: {list(summary.keys())}")
        
        success_rate_percent = summary['results/success_rate_percent']
        
        # Get total files for this dataset
        if 'results/total_files' not in summary:
            raise ValueError(f"Could not find total files in W&B summary for run {run.name}. Available keys: {list(summary.keys())}")
        
        total_files = summary['results/total_files']
        
        # Store file count for this dataset - validate consistency
        if dataset in dataset_file_counts:
            if dataset_file_counts[dataset] != total_files:
                raise ValueError(f"File count mismatch for dataset '{dataset}': "
                               f"previously found {dataset_file_counts[dataset]} files, "
                               f"but run {run.name} reports {total_files} files")
        else:
            dataset_file_counts[dataset] = total_files
        
        # Map model name
        model_name = MODEL_MAPPING.get(llm_provider, llm_provider)
        
        results[model_name][dataset] = success_rate_percent  # Already in percentage
        
        print(f"Found: {model_name} + {dataset} = {success_rate_percent:.1f}% ({total_files} files)")
    
    return results, dataset_file_counts

def generate_latex_table(results, dataset_file_counts):
    """Generate LaTeX table rows for the Lean section."""
    
    latex_lines = []
    latex_lines.append("\\newcommand{\\statsLean}{")
    latex_lines.append("% exp no.  & numpy & dbench & heval & verina & bignum & proofsynth & APPS & totals")
    
    # Build header with actual file counts
    header_counts = []
    total_files = 0
    for col in COLUMN_ORDER:
        if col in dataset_file_counts:
            count = dataset_file_counts[col]
            header_counts.append(f"{count} tasks")
            total_files += count
        else:
            header_counts.append("")
    
    latex_lines.append(f"\\langHeader{{\\large Lean}}{{{header_counts[0]}}}{{{header_counts[1]}}}{{{header_counts[2]}}}{{{header_counts[3]}}}{{{header_counts[4]}}}{{{header_counts[5]}}}{{{header_counts[6]}}}{{\\textbf{{{total_files} tasks}}}} \\\\")
    latex_lines.append("\\hline")
    
    # Generate rows for each model
    for model in MODEL_MAPPING.values():
        if model in results:
            # Build the stats row
            row_data = [f"\\textbf{{{model}}}, spec"]
            
            for col in COLUMN_ORDER:
                if col in results[model]:
                    value = results[model][col]
                    row_data.append(f"{value:.1f}")  # Include 0.0% results
                else:
                    row_data.append("")  # Only empty if no data exists
            
            # Add empty total column for now
            row_data.append("")
            
            # Create the stats line
            stats_line = "\\stats{" + "}{".join(row_data) + "} \\\\"
            latex_lines.append(stats_line)
            
            # Skip the "spec,vibe" row as requested
            latex_lines.append("\\hline")
    
    # Add model union placeholder (empty as requested)
    latex_lines.append("\\hline")
    latex_lines.append("\\statsgray{\\textbf{MODEL UNION}, spec}")
    latex_lines.append("{\\numpyResLean}{\\dbResLean}{\\heResLean}{\\verinaResLean}{\\bignumResLean}{\\verifResLean}{\\appsResLean}{\\totalResLean}{} \\\\")
    latex_lines.append("\\hline")
    latex_lines.append("}")
    
    return "\n".join(latex_lines)

def main():
    parser = argparse.ArgumentParser(description="Generate LaTeX table from W&B results")
    parser.add_argument("--tag", required=True, help="W&B tag to filter results")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set")
        return
    
    print(f"Fetching results for tag: {args.tag}")
    results, dataset_file_counts = get_wandb_results(args.tag, args.project, args.entity, args.debug)
    
    if not results:
        print("No results found for the specified tag")
        return
    
    print(f"\nFound results for {len(results)} models")
    print(f"Dataset file counts: {dataset_file_counts}")
    
    latex_table = generate_latex_table(results, dataset_file_counts)
    
    print("\n" + "="*60)
    print("LaTeX table (paste into A5-experiments.tex):")
    print("="*60)
    print(latex_table)

if __name__ == "__main__":
    main()