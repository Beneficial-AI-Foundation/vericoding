#!/usr/bin/env python3
"""
Extract W&B results for multiple tags (same dataset, different models) and display in simple format.
"""

import argparse
import wandb
import os
import sys
from collections import defaultdict
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

# Model name mapping and fixed order
MODEL_ORDER = [
    'claude-opus-4.1',
    'claude-sonnet-4', 
    'deepseek-chat-v3.1',
    'gemini-2.5-pro',
    'gemini-2.5-flash',
    'glm-4.5',
    'gpt-5',
    'gpt-5-mini',
    'grok-4',
    'grok-code'
]

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

def get_wandb_results_for_tags(tags, project="vericoding", entity=None, debug=False):
    """Fetch results from W&B for multiple tags."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    # Combine all tags in the filter
    runs = api.runs(project_path, filters={"tags": {"$in": tags}})
    
    # Store per-shard results for aggregation
    shard_results = defaultdict(list)  # model_name -> list of {'success_rate': float, 'successful_files': int, 'total_files': int, 'url': str, 'files_dir': str}
    detailed_results = defaultdict(lambda: defaultdict(list))  # dataset -> model -> list of table_data
    dataset_name = None
    dataset_file_count = None
    
    for i, run in enumerate(runs):
        # Get model and dataset info
        config = run.config
        summary = run.summary
        
        # Debug: print first few run structures
        if debug and i < 3:
            print(f"\nDEBUG: Run {run.name}", file=sys.stderr)
            print(f"Config keys: {list(config.keys())}", file=sys.stderr)
            print(f"Summary keys: {list(summary.keys())}", file=sys.stderr)
            print(f"Tags: {run.tags}", file=sys.stderr)
            print("-" * 50, file=sys.stderr)
        
        llm = config.get('llm', '')
        language = config.get('language', '')
        
        # Skip non-Lean runs
        if language != 'lean':
            continue
        
        # Check if this run has results
        if 'results/success_rate_percent' not in summary:
            if debug:
                print(f"Skipping run {run.name} - no success rate", file=sys.stderr)
            continue
        
        success_rate_percent = summary['results/success_rate_percent']
        
        if 'results/total_files' not in summary or 'results/successful_files' not in summary:
            if debug:
                print(f"Skipping run {run.name} - missing file counts", file=sys.stderr)
            continue
        
        total_files = summary['results/total_files']
        successful_files = summary['results/successful_files']
        
        # Map model name
        model_name = MODEL_MAPPING.get(llm, llm)
        
        # Get files_dir for dataset identification
        files_dir = config.get('files_dir', 'unknown')
        
        # Store shard results (append to list for aggregation)
        shard_results[model_name].append({
            'success_rate': success_rate_percent,
            'successful_files': successful_files,
            'total_files': total_files,
            'url': run.url,
            'files_dir': files_dir
        })
        
        # Get detailed results for model union calculation
        if 'detailed_results' in summary:
            try:
                detailed_table_ref = summary['detailed_results']
                table_path = detailed_table_ref.get('path')
                if table_path:
                    # Download the table file from the run
                    table_file = run.file(table_path)
                    downloaded_file = table_file.download(replace=True)
                    
                    # Read the JSON table data
                    import json
                    with open(downloaded_file.name, 'r') as f:
                        detailed_table = json.load(f)
                    
                    # Clean up downloaded file
                    os.remove(downloaded_file.name)
                    
                    # Store detailed results (append to list for aggregation)
                    detailed_results['dataset'][model_name].append(detailed_table)
                    
            except Exception as e:
                if debug:
                    print(f"Could not download detailed results for {model_name}: {e}", file=sys.stderr)
        
        print(f"Found shard: {model_name} = {success_rate_percent:.1f}% ({successful_files}/{total_files} files) - {run.url}", file=sys.stderr)
    
    # Aggregate shard results for each model
    results = {}
    for model_name, shards in shard_results.items():
        if shards:
            # Sum up successful files and total files across shards
            total_successful = sum(s['successful_files'] for s in shards)
            total_files = sum(s['total_files'] for s in shards)
            
            # Calculate aggregated success rate
            aggregated_success_rate = (total_successful / total_files * 100) if total_files > 0 else 0
            
            # Collect all URLs
            urls = [s['url'] for s in shards]
            
            # Use files_dir from first shard (should be same across all shards)
            files_dir = shards[0]['files_dir']
            
            results[model_name] = {
                'success_rate': aggregated_success_rate,
                'successful_files': total_successful,
                'total_files': total_files,
                'url': urls[0] if len(urls) == 1 else f"[{len(urls)} shards]",
                'files_dir': files_dir,
                'shard_count': len(shards),
                'shard_urls': urls
            }
            
            print(f"Aggregated: {model_name} = {aggregated_success_rate:.1f}% ({total_successful}/{total_files} files across {len(shards)} shard(s))", file=sys.stderr)
            
            # Update dataset file count
            if dataset_file_count is None:
                dataset_file_count = total_files
    
    return results, dataset_file_count, detailed_results

def calculate_model_union(detailed_results, dataset_file_count):
    """Calculate model union results - file succeeds if ANY model succeeds on it."""
    if 'dataset' not in detailed_results:
        return None
    
    # Collect all files across all models
    all_files = set()
    file_success = {}  # filename -> bool (True if any model succeeded)
    
    for model_name, table_data_list in detailed_results['dataset'].items():
        # Now table_data_list is a list of tables (one per shard)
        for table_data in table_data_list:
            if table_data and 'data' in table_data:
                # Parse the JSON table data to get individual file results
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
        return {
            'success_rate': (successful_files / total_files) * 100,
            'successful_files': successful_files,
            'total_files': total_files
        }
    else:
        return {
            'success_rate': 0.0,
            'successful_files': 0,
            'total_files': dataset_file_count
        }

def main():
    parser = argparse.ArgumentParser(description="Display W&B results for multiple tags in simple format")
    parser.add_argument("--tags", required=True, nargs='+', help="W&B tags to fetch results for")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    print(f"Fetching results for tags: {', '.join(args.tags)}", file=sys.stderr)
    results, dataset_file_count, detailed_results = get_wandb_results_for_tags(args.tags, args.project, args.entity, args.debug)
    
    if not results:
        print("No results found for the specified tags", file=sys.stderr)
        return
    
    print(f"\nDataset has {dataset_file_count} files", file=sys.stderr)
    print(f"Found results for {len(results)} models\n", file=sys.stderr)
    
    # Print results in fixed model order
    print("# Model Results")
    for model in MODEL_ORDER:
        if model in results:
            data = results[model]
            shard_info = f" ({data['shard_count']} shards)" if data.get('shard_count', 1) > 1 else ""
            # Check if total files differs from dataset file count
            if dataset_file_count and data['total_files'] != dataset_file_count:
                file_warning = f" ⚠️ {data['successful_files']}/{data['total_files']} files"
                print(f"\033[93m% WARNING: {model} has different file count: {data['total_files']} vs expected {dataset_file_count}\033[0m", file=sys.stderr)
            else:
                file_warning = f" {data['successful_files']}/{data['total_files']} files"
            print(f"% {model}\t{data['files_dir']}\t{data['success_rate']:.1f}\\%{file_warning}{shard_info}\t{data['url']}")
        else:
            print(f"% {model}\tunknown\t--\t--")
    
    # Only calculate and print model union if we have results and no unknown models
    has_unknown_models = any(model not in results for model in MODEL_ORDER if model in results) or \
                        any(data['files_dir'] == 'unknown' for data in results.values())
    
    if not has_unknown_models and results:
        union_result = calculate_model_union(detailed_results, dataset_file_count)
        
        # Get files_dir from any available result for union row
        union_files_dir = next(iter(results.values()))['files_dir']
        
        if union_result:
            print(f"\n# Model Union")
            print(f"% MODEL_UNION\t{union_files_dir}\t{union_result['success_rate']:.1f}\\%\t--")
            print(f"# Union: {union_result['successful_files']}/{union_result['total_files']} files")
        else:
            print(f"\n# Model Union")
            print(f"% MODEL_UNION\t{union_files_dir}\t--\t-- (no detailed results available)")
    else:
        print(f"\n# Model Union")
        print("# Skipping model union - some models have unknown files_dir")

if __name__ == "__main__":
    main()
