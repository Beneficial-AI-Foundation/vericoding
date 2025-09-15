#!/usr/bin/env python3
"""
Examine the structure of detailed_results from W&B summary.
"""

import argparse
import wandb
import os
import sys
import json
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

def examine_detailed_results(tag, project="vericoding", entity=None):
    """Examine detailed_results structure from W&B runs."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    runs = api.runs(project_path, filters={"tags": {"$in": [tag]}})
    
    for i, run in enumerate(runs):
        print(f"\n=== Run {i}: {run.name} ===", file=sys.stderr)
        
        config = run.config
        summary = run.summary
        
        # Get basic info
        llm_provider = config.get('llm_provider', '')
        language = config.get('language', '')
        
        print(f"Provider: {llm_provider}, Language: {language}", file=sys.stderr)
        
        if language != 'lean':
            continue
            
        if 'detailed_results' in summary:
            detailed_results = summary['detailed_results']
            print(f"detailed_results type: {type(detailed_results)}", file=sys.stderr)
            
            # Examine the keys and structure
            try:
                keys = list(detailed_results.keys())
                print(f"Keys: {keys}", file=sys.stderr)
                print(f"Table dimensions: {detailed_results.get('nrows')} rows x {detailed_results.get('ncols')} cols", file=sys.stderr)
                
                # Try to fetch the actual table data using the run's files
                try:
                    # Get the table file directly from the run
                    table_path = detailed_results.get('path')
                    if table_path:
                        print(f"Trying to download file: {table_path}", file=sys.stderr)
                        
                        # Download the file from the run
                        table_file = run.file(table_path)
                        table_data = table_file.download(replace=True)
                        
                        # Read the downloaded JSON file
                        import json
                        with open(table_data.name, 'r') as f:
                            table_json = json.load(f)
                        
                        print(f"Table JSON keys: {list(table_json.keys())}", file=sys.stderr)
                        
                        if 'columns' in table_json:
                            print(f"Columns: {table_json['columns']}", file=sys.stderr)
                        
                        if 'data' in table_json:
                            print(f"Data rows: {len(table_json['data'])}", file=sys.stderr)
                            if table_json['data']:
                                print(f"First 3 data rows:", file=sys.stderr)
                                for idx, row in enumerate(table_json['data'][:3]):
                                    print(f"  Row {idx}: {row}", file=sys.stderr)
                        
                        # Clean up downloaded file
                        import os
                        os.remove(table_data.name)
                    
                except Exception as table_e:
                    print(f"Error fetching table data: {table_e}", file=sys.stderr)
                    
            except Exception as e:
                print(f"Error examining keys: {e}", file=sys.stderr)
        else:
            print(f"No detailed_results in summary. Available keys: {list(summary.keys())}", file=sys.stderr)
        
        if i >= 2:  # Only examine first few runs
            break

def main():
    parser = argparse.ArgumentParser(description="Examine detailed_results structure")
    parser.add_argument("--tag", required=True, help="W&B tag to filter results")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    examine_detailed_results(args.tag, args.project, args.entity)

if __name__ == "__main__":
    main()