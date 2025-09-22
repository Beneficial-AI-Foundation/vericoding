#!/usr/bin/env python3
"""
Extract detailed_results table from a specific W&B run and test final_output column with lake build.
"""

import argparse
import wandb
import os
import sys
import json
import subprocess
from pathlib import Path
from dotenv import load_dotenv

# Load environment variables
load_dotenv()

def get_run_detailed_results(run_id, project="vericoding", entity=None, debug=False):
    """Fetch detailed results table from a specific W&B run."""
    api = wandb.Api()
    
    # Get project path
    if entity:
        project_path = f"{entity}/{project}"
    else:
        project_path = project
    
    try:
        run = api.run(f"{project_path}/{run_id}")
    except Exception as e:
        raise ValueError(f"Could not find run {run_id} in project {project_path}: {e}")
    
    # Debug: print run structure
    if debug:
        print(f"\nDEBUG: Run {run.name} ({run_id})", file=sys.stderr)
        config = run.config
        summary = run.summary
        print(f"Config keys: {list(config.keys())}", file=sys.stderr)
        print(f"Summary keys: {list(summary.keys())}", file=sys.stderr)
        print("-" * 50, file=sys.stderr)
    
    # Get detailed results from summary
    if 'detailed_results' not in run.summary:
        raise ValueError(f"Could not find detailed_results in W&B summary for run {run_id}. Available keys: {list(run.summary.keys())}")
    
    detailed_table_ref = run.summary['detailed_results']
    
    # Download the actual table data
    try:
        table_path = detailed_table_ref.get('path')
        if not table_path:
            raise ValueError(f"No path found in detailed_results for run {run_id}")
            
        # Download the table file from the run
        table_file = run.file(table_path)
        downloaded_file = table_file.download(replace=True)
        
        # Read the JSON table data
        with open(downloaded_file.name, 'r') as f:
            detailed_table = json.load(f)
        
        # Clean up downloaded file
        os.remove(downloaded_file.name)
        
    except Exception as e:
        raise ValueError(f"Could not download detailed_results table for run {run_id}: {e}")
    
    return detailed_table, run

def get_guard_msgs_from_yaml(file_name, project_root=None, debug=False):
    """Extract guard_msgs from the corresponding YAML file."""
    if project_root is None:
        project_root = Path.cwd()
    else:
        project_root = Path(project_root)
    
    # Convert .lean filename to .yaml filename
    yaml_name = file_name.replace('.lean', '.yaml')
    yaml_path = project_root / "benchmarks" / "lean" / "fvapps" / "yaml" / yaml_name
    
    if not yaml_path.exists():
        return ""
    
    try:
        import yaml
        with open(yaml_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        # Extract vc-postamble section
        postamble = data.get('vc-postamble', '')
        if not postamble:
            return ""
        
        # Extract guard_msgs patterns from postamble
        import re
        guard_patterns = re.findall(
            r'(/--\s*\n\s*info:\s*[^\n]+\s*\n\s*-/\s*\n\s*#guard_msgs in\s*\n\s*#eval[^\n]+)',
            postamble,
            re.MULTILINE | re.DOTALL
        )
        
        return '\n\n'.join(guard_patterns) if guard_patterns else ""
        
    except Exception as e:
        if debug:
            print(f"Warning: Could not extract guard_msgs from {yaml_path}: {e}", file=sys.stderr)
        return ""

def test_lean_code_with_lake(code, test_name="test", project_root=None, debug=False):
    """Test Lean code using lake build in the existing project structure."""
    if not code or not code.strip():
        return False, "Empty code"
    
    if project_root is None:
        project_root = Path.cwd()
    else:
        project_root = Path(project_root)
    
    # Create a temporary test file in the lean directory
    lean_dir = project_root / "lean"
    lean_dir.mkdir(exist_ok=True)
    
    # Create a unique test file name
    test_file = lean_dir / f"test_{test_name.replace('.', '_')}.lean"
    
    try:
        # Get guard_msgs from corresponding YAML file
        guard_msgs = get_guard_msgs_from_yaml(test_name, project_root, debug)
        
        # Combine the generated code with guard_msgs
        full_code = code
        if guard_msgs:
            full_code += "\n\n" + guard_msgs
            if debug:
                print("  Added guard_msgs from YAML file", file=sys.stderr)
        
        # Write the combined code to the test file
        with open(test_file, "w") as f:
            f.write(full_code)
        
        # Run lake env to check the Lean code syntax and type-checking
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(test_file)],
                cwd=project_root,
                capture_output=True,
                text=True,
                timeout=60  # 60 second timeout
            )
            
            success = result.returncode == 0
            
            if debug:
                print(f"Lake env result for {test_name}:", file=sys.stderr)
                print(f"Return code: {result.returncode}", file=sys.stderr)
                if result.stdout:
                    print(f"STDOUT: {result.stdout}", file=sys.stderr)
                if result.stderr:
                    print(f"STDERR: {result.stderr}", file=sys.stderr)
            
            return success, result.stderr if result.stderr else result.stdout
            
        except subprocess.TimeoutExpired:
            return False, "Build timed out after 60 seconds"
        except Exception as e:
            return False, f"Build failed with exception: {e}"
    
    finally:
        # Clean up the test file
        if test_file.exists():
            test_file.unlink()

def main():
    parser = argparse.ArgumentParser(description="Test final_output column from W&B detailed_results with lake build")
    parser.add_argument("--run-id", required=True, help="W&B run ID to fetch detailed results from")
    parser.add_argument("--project", default="vericoding", help="W&B project name")
    parser.add_argument("--entity", help="W&B entity/username")
    parser.add_argument("--debug", action="store_true", help="Enable debug output")
    parser.add_argument("--max-tests", type=int, default=10, help="Maximum number of tests to run")
    parser.add_argument("--output-dir", help="Directory to save test results (optional)")
    
    args = parser.parse_args()
    
    # Check for W&B API key
    if not os.getenv("WANDB_API_KEY"):
        print("Error: WANDB_API_KEY environment variable not set", file=sys.stderr)
        return 1
    
    # Check for lake command
    try:
        subprocess.run(["lake", "--version"], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("Error: 'lake' command not found. Please ensure Lean 4 is installed.", file=sys.stderr)
        return 1
    
    print(f"Fetching detailed results from run: {args.run_id}", file=sys.stderr)
    
    try:
        detailed_table, run = get_run_detailed_results(args.run_id, args.project, args.entity, args.debug)
    except Exception as e:
        print(f"Error fetching run data: {e}", file=sys.stderr)
        return 1
    
    if not detailed_table or 'data' not in detailed_table:
        print("Error: No data found in detailed_results table", file=sys.stderr)
        return 1
    
    # Parse the table data
    # Expected columns: ['file_name', 'subfolder', 'success', 'output_file', 'error_message', 'has_bypass', 'file_path', 'original_spec', 'final_output', 'debug_files', 'generate_prompt', 'fix_prompts']
    data = detailed_table['data']
    
    print(f"Found {len(data)} rows in detailed_results table", file=sys.stderr)
    
    # Test results
    test_results = []
    successful_tests = 0
    total_tests = min(len(data), args.max_tests)
    
    for i, row in enumerate(data[:args.max_tests]):
        if len(row) < 10:  # Need at least 10 columns to get final_output
            print(f"Warning: Row {i} has insufficient columns ({len(row)}), skipping", file=sys.stderr)
            continue
        
        file_name = row[0]  # file_name
        success = row[2]    # success
        final_output = row[8]  # final_output
        
        print(f"\nTesting {i+1}/{total_tests}: {file_name}", file=sys.stderr)
        print(f"  Original success: {success}", file=sys.stderr)
        
        # Test the final_output with lake build
        lake_success, lake_output = test_lean_code_with_lake(final_output, file_name, project_root=Path.cwd(), debug=args.debug)
        
        test_result = {
            'file_name': file_name,
            'original_success': success,
            'lake_success': lake_success,
            'lake_output': lake_output,
            'final_output': final_output
        }
        test_results.append(test_result)
        
        if lake_success:
            successful_tests += 1
            print("  ✓ Lake build: SUCCESS", file=sys.stderr)
        else:
            print("  ✗ Lake build: FAILED", file=sys.stderr)
            if not args.debug and lake_output:
                # Show first few lines of error
                error_lines = lake_output.split('\n')[:3]
                for line in error_lines:
                    if line.strip():
                        print(f"    {line.strip()}", file=sys.stderr)
    
    # Summary
    print("\n" + "="*60, file=sys.stderr)
    print("SUMMARY", file=sys.stderr)
    print(f"Total tests: {total_tests}", file=sys.stderr)
    print(f"Lake build successes: {successful_tests}", file=sys.stderr)
    print(f"Lake build success rate: {(successful_tests/total_tests)*100:.1f}%", file=sys.stderr)
    
    # Save results if output directory specified
    if args.output_dir:
        output_path = Path(args.output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Save detailed results as JSON
        results_file = output_path / f"test_results_{args.run_id}.json"
        with open(results_file, 'w') as f:
            json.dump({
                'run_id': args.run_id,
                'total_tests': total_tests,
                'successful_tests': successful_tests,
                'success_rate': (successful_tests/total_tests)*100,
                'test_results': test_results
            }, f, indent=2)
        
        print(f"Detailed results saved to: {results_file}", file=sys.stderr)
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
