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
            
            if hasattr(detailed_results, 'data'):
                print(f"Has .data attribute with {len(detailed_results.data)} rows", file=sys.stderr)
                print(f"Columns: {detailed_results.columns if hasattr(detailed_results, 'columns') else 'No columns attr'}", file=sys.stderr)
                
                if detailed_results.data:
                    print(f"First 3 rows:", file=sys.stderr)
                    for idx, row in enumerate(detailed_results.data[:3]):
                        print(f"  Row {idx}: {row} (type: {type(row)})", file=sys.stderr)
            else:
                print(f"No .data attribute. Content: {str(detailed_results)[:200]}...", file=sys.stderr)
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