#!/usr/bin/env python3
"""
Extract W&B results for a specific tag and generate LaTeX table for vericoding paper.
"""

import argparse
import wandb
import os
import sys
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
    run_urls = defaultdict(lambda: defaultdict(str))  # Track W&B URLs for each model+dataset
    detailed_results = defaultdict(lambda: defaultdict(dict))  # Track detailed results per dataset+model
    
    for i, run in enumerate(runs):
        # Get model and dataset info
        config = run.config
        summary = run.summary
        
        # Debug: print first few run structures
        if debug and i < 3:
            print(f"\nDEBUG: Run {run.name}", file=sys.stderr)
            print(f"Config keys: {list(config.keys())}", file=sys.stderr)
            print(f"Summary keys: {list(summary.keys())}", file=sys.stderr)
            print(f"Config: {dict(config)}", file=sys.stderr)
            print(f"Summary: {dict(summary)}", file=sys.stderr)
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
                print(f"  folder: '{folder}'", file=sys.stderr)
                print(f"  files_dir: '{files_dir}'", file=sys.stderr)
                print(f"  dataset_path: '{dataset_path}'", file=sys.stderr)
                print(f"  spec_folder: '{spec_folder}'", file=sys.stderr)
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
        
        # Get successful files for total calculation
        if 'results/successful_files' not in summary:
            raise ValueError(f"Could not find successful files in W&B summary for run {run.name}. Available keys: {list(summary.keys())}")
        
        successful_files = summary['results/successful_files']
        
        # Map model name
        model_name = MODEL_MAPPING.get(llm_provider, llm_provider)
        
        # Store results with additional metadata
        results[model_name][dataset] = {
            'success_rate': success_rate_percent,
            'successful_files': successful_files,
            'total_files': total_files
        }
        
        # Store W&B URL for this run
        run_urls[model_name][dataset] = run.url
        
        # Get detailed results from summary
        if 'detailed_results' not in summary:
            raise ValueError(f"Could not find detailed_results in W&B summary for run {run.name} ({model_name} + {dataset}). Available keys: {list(summary.keys())}")
        
        detailed_table_ref = summary['detailed_results']
        
        # Download the actual table data
        try:
            table_path = detailed_table_ref.get('path')
            if not table_path:
                raise ValueError(f"No path found in detailed_results for run {run.name} ({model_name} + {dataset})")
                
            # Download the table file from the run
            table_file = run.file(table_path)
            downloaded_file = table_file.download(replace=True)
            
            # Read the JSON table data
            import json
            with open(downloaded_file.name, 'r') as f:
                detailed_table = json.load(f)
            
            # Clean up downloaded file
            import os
            os.remove(downloaded_file.name)
            
        except Exception as e:
            raise ValueError(f"Could not download detailed_results table for run {run.name} ({model_name} + {dataset}): {e}")
        
        # Store detailed results for this model+dataset
        detailed_results[dataset][model_name] = detailed_table
        print(f"  Loaded detailed results for {model_name} + {dataset}", file=sys.stderr)
        
        print(f"Found: {model_name} + {dataset} = {success_rate_percent:.1f}% ({successful_files}/{total_files} files)", file=sys.stderr)
    
    return results, dataset_file_counts, run_urls, detailed_results

def calculate_model_union(detailed_results, dataset_file_counts):
    """Calculate model union results - file succeeds if ANY model succeeds on it."""
    union_results = {}
    
    for dataset in COLUMN_ORDER:
        if dataset in detailed_results and dataset in dataset_file_counts:
            # Collect all files across all models for this dataset
            all_files = set()
            file_success = {}  # filename -> bool (True if any model succeeded)
            
            for model_name, table_data in detailed_results[dataset].items():
                if table_data and 'data' in table_data:
                    # Parse the JSON table data to get individual file results
                    # Columns: ['file_name', 'subfolder', 'success', 'output_file', 'error_message', 'has_bypass', 'file_path', 'original_spec', 'final_output', 'debug_files', 'generate_prompt', 'fix_prompts']
                    for row in table_data['data']:
                        if len(row) >= 3:  # Need at least file_name, subfolder, success
                            filename = row[0]  # file_name is first column
                            success = row[2]   # success is third column (index 2)
                            
                            all_files.add(filename)
                            if filename not in file_success:
                                file_success[filename] = False
                            
                            # File succeeds if ANY model succeeded on it
                            if success:
                                file_success[filename] = True
            
            # Calculate union success rate
            if all_files:
                successful_files = sum(1 for success in file_success.values() if success)
                total_files = len(all_files)
                union_results[dataset] = {
                    'success_rate': (successful_files / total_files) * 100,
                    'successful_files': successful_files,
                    'total_files': total_files
                }
            else:
                union_results[dataset] = {
                    'success_rate': 0.0,
                    'successful_files': 0,
                    'total_files': dataset_file_counts[dataset]
                }
    
    return union_results

def generate_latex_table(results, dataset_file_counts, run_urls, detailed_results, tag):
    """Generate LaTeX table rows for the Lean section."""
    
    latex_lines = []
    latex_lines.append(f"% Generated from uv run src/scripts/wandb_to_latex.py --tag {tag}")
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
            # Generate URL comments for this model
            for col in COLUMN_ORDER:
                if col in results[model]:
                    url = run_urls[model][col]
                    latex_lines.append(f"% {model} + {col}: {url}")
            
            # Build the stats row
            row_data = [f"\\textbf{{{model}}}, spec"]
            
            # Calculate totals for this model
            total_successful = 0
            total_files = 0
            
            for col in COLUMN_ORDER:
                if col in results[model]:
                    data = results[model][col]
                    success_rate = data['success_rate']
                    
                    # Add just the success rate
                    row_data.append(f"{success_rate:.1f}")
                    
                    # Add to totals
                    total_successful += data['successful_files']
                    total_files += data['total_files']
                else:
                    row_data.append("")  # Only empty if no data exists
            
            # Calculate and add total success rate
            if total_files > 0:
                total_rate = (total_successful / total_files) * 100
                row_data.append(f"{total_rate:.1f}")
            else:
                row_data.append("")
            
            # Create the stats line
            stats_line = "\\stats{" + "}{".join(row_data) + "} \\\\"
            latex_lines.append(stats_line)
            
            # Skip the "spec,vibe" row as requested
            latex_lines.append("\\hline")
    
    # Add model union row
    latex_lines.append("\\hline")
    
    # Calculate model union results
    union_results = calculate_model_union(detailed_results, dataset_file_counts)
    
    # Build union row
    union_row_data = ["\\textbf{MODEL UNION}, spec"]
    union_total_successful = 0
    union_total_files = 0
    
    for col in COLUMN_ORDER:
        if col in union_results:
            success_rate = union_results[col]['success_rate']
            union_row_data.append(f"{success_rate:.1f}")
            union_total_successful += union_results[col]['successful_files']
            union_total_files += union_results[col]['total_files']
        else:
            union_row_data.append("")
    
    # Calculate overall union total
    if union_total_files > 0:
        union_total_rate = (union_total_successful / union_total_files) * 100
        union_row_data.append(f"{union_total_rate:.1f}")
    else:
        union_row_data.append("")
    
    union_stats_line = "\\statsgray{" + "}{".join(union_row_data) + "} \\\\"
    latex_lines.append(union_stats_line)
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
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    print(f"Fetching results for tag: {args.tag}", file=sys.stderr)
    results, dataset_file_counts, run_urls, detailed_results = get_wandb_results(args.tag, args.project, args.entity, args.debug)
    
    if not results:
        print("No results found for the specified tag", file=sys.stderr)
        return
    
    print(f"\nFound results for {len(results)} models", file=sys.stderr)
    print(f"Dataset file counts: {dataset_file_counts}", file=sys.stderr)
    
    latex_table = generate_latex_table(results, dataset_file_counts, run_urls, detailed_results, args.tag)
    
    # Output only the LaTeX table to stdout
    print(latex_table)

if __name__ == "__main__":
    main()