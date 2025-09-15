#!/usr/bin/env python3
"""
Examine W&B artifacts to understand their structure for debugging.
"""

import argparse
import wandb
import os
import sys
import json
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

def examine_run_artifacts(tag, project="vericoding", entity=None, run_name=None):
    """Examine artifacts from W&B runs for a specific tag."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    runs = api.runs(project_path, filters={"tags": {"$in": [tag]}})
    
    for i, run in enumerate(runs):
        if run_name and run.name != run_name:
            continue
            
        print(f"\n=== Run {i}: {run.name} ===", file=sys.stderr)
        print(f"Config: {dict(run.config)}", file=sys.stderr)
        print(f"Summary keys: {list(run.summary.keys())}", file=sys.stderr)
        
        # List all artifacts
        print(f"\nArtifacts for {run.name}:", file=sys.stderr)
        artifacts = list(run.logged_artifacts())
        if not artifacts:
            print("  No artifacts found", file=sys.stderr)
        else:
            for j, artifact in enumerate(artifacts):
                print(f"  {j}: {artifact.name} (type: {artifact.type})", file=sys.stderr)
                
                # List files in the artifact
                try:
                    files = artifact.files()
                    print(f"    Files:", file=sys.stderr)
                    for file_obj in files:
                        print(f"      - {file_obj.name} (size: {file_obj.size})", file=sys.stderr)
                except Exception as e:
                    print(f"    Error listing files: {e}", file=sys.stderr)
        
        # If this is the run we're looking for, examine the first artifact in detail
        if run_name and run.name == run_name and artifacts:
            print(f"\n=== Examining first artifact in detail ===", file=sys.stderr)
            artifact = artifacts[0]
            
            try:
                files = artifact.files()
                for file_obj in files:
                    print(f"\nExamining file: {file_obj.name}", file=sys.stderr)
                    
                    # Try to download and examine the content
                    try:
                        if file_obj.name.endswith('.json'):
                            content = artifact.get(file_obj.name)
                            if hasattr(content, 'data'):
                                print(f"  Type: W&B Table with {len(content.data)} rows", file=sys.stderr)
                                print(f"  Columns: {content.columns}", file=sys.stderr)
                                if content.data:
                                    print(f"  First few rows:", file=sys.stderr)
                                    for idx, row in enumerate(content.data[:3]):
                                        print(f"    Row {idx}: {row}", file=sys.stderr)
                            else:
                                # Regular JSON
                                print(f"  Content preview: {str(content)[:200]}...", file=sys.stderr)
                        else:
                            print(f"  Non-JSON file, skipping content examination", file=sys.stderr)
                    except Exception as e:
                        print(f"  Error examining content: {e}", file=sys.stderr)
                        
            except Exception as e:
                print(f"Error examining artifact: {e}", file=sys.stderr)
        
        if i >= 2:  # Limit to first 3 runs for brevity
            break

def main():
    parser = argparse.ArgumentParser(description="Examine W&B artifacts")
    parser.add_argument("--tag", required=True, help="W&B tag to filter results")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--run-name", help="Specific run name to examine in detail")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return
    
    examine_run_artifacts(args.tag, args.project, args.entity, args.run_name)

if __name__ == "__main__":
    main()