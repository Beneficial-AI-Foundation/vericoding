#!/usr/bin/env python3
"""
Vericode Printer Module
Handles summary generation, results formatting, and output display.
"""

import os
import json
import csv
import subprocess
from datetime import datetime
from pathlib import Path
from urllib.parse import quote
from vericode_parser import count_atoms_and_specs

def get_git_remote_url():
    """
    Get the GitHub remote URL from git configuration.
    Returns:
        str: GitHub repository URL or None if not found
    """
    try:
        result = subprocess.run(['git', 'config', '--get', 'remote.origin.url'], 
                              capture_output=True, text=True, check=True)
        remote_url = result.stdout.strip()
        if remote_url.startswith('git@github.com:'):
            remote_url = remote_url.replace('git@github.com:', 'https://github.com/')
            remote_url = remote_url.replace('.git', '')
        elif remote_url.startswith('https://github.com/'):
            remote_url = remote_url.replace('.git', '')
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
            return None
        return remote_url
    except subprocess.CalledProcessError:
        print("Error: Could not get git remote URL. Make sure you're in a git repository.")
        return None
    except Exception as e:
        print(f"Error getting git remote URL: {e}")
        return None

def get_current_branch():
    """
    Get the current git branch.
    Returns:
        str: Current branch name or 'main' as default
    """
    try:
        result = subprocess.run(['git', 'branch', '--show-current'], 
                              capture_output=True, text=True, check=True)
        return result.stdout.strip()
    except:
        try:
            result = subprocess.run(['git', 'rev-parse', '--abbrev-ref', 'HEAD'], 
                                  capture_output=True, text=True, check=True)
            return result.stdout.strip()
        except:
            print("Warning: Could not determine current branch. Using 'main' as default.")
            return 'main'

def get_github_url(file_path, repo_url, branch="main"):
    repo_url = repo_url.rstrip('/')
    encoded_path = quote(str(file_path))
    github_url = f"{repo_url}/blob/{branch}/{encoded_path}"
    return github_url

def get_repo_root():
    """
    Find the repository root by looking for .git directory.
    For GitHub links, prefer the parent repository if we're in a subdirectory
    that has its own .git but should be part of the parent repo structure.
    Returns:
        Path: Repository root path
    """
    current = Path.cwd()
    
    # First, check if we're in a subdirectory that should use the parent repo
    # This handles cases where a subdirectory has its own .git but should be
    # part of the parent repository structure for GitHub links
    if current.name == "dafny" and (current.parent / '.git').exists():
        return current.parent
    
    # Normal repository root detection
    while current != current.parent:
        if (current / '.git').exists():
            return current
        current = current.parent
    
    # If we didn't find .git in current directory tree, 
    # check if we're in a subdirectory of a git repo
    current = Path.cwd()
    while current != current.parent:
        if (current.parent / '.git').exists():
            return current.parent
        current = current.parent
    
    return Path.cwd()  # Fallback to current directory

def get_github_path(file_path, repo_root):
    """
    Get consistent GitHub path regardless of file location.
    
    Args:
        file_path: Path to the file (can be absolute or relative)
        repo_root: Repository root path
    
    Returns:
        Path: Path relative to repository root for GitHub URL
    """
    # Ensure file_path is absolute
    if not file_path.is_absolute():
        file_path = file_path.resolve()
    
    try:
        # Try relative to repo root first (preferred method)
        rel_to_repo = file_path.relative_to(repo_root)
        return rel_to_repo
    except ValueError:
        # If that fails, try relative to current working directory
        try:
            rel_to_current = file_path.relative_to(Path.cwd())
            # Get the path from current directory to repo root
            current_to_repo = Path.cwd().relative_to(repo_root)
            # Combine the paths
            return current_to_repo / rel_to_current
        except ValueError:
            # If both fail, construct a path that should work
            # This handles cases where the file is outside the repo structure
            return file_path.name

def print_summary(results, output_dir):
    """Print a summary of the results."""
    total_files = len(results)
    successful_files = sum(1 for r in results if r['success'])
    failed_files = total_files - successful_files
    
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Total files processed: {total_files}")
    print(f"Successful: {successful_files}")
    print(f"Failed: {failed_files}")
    print(f"Success rate: {successful_files/total_files*100:.1f}%" if total_files > 0 else "N/A")
    
    if failed_files > 0:
        print(f"\nFailed files:")
        for result in results:
            if not result['success']:
                print(f"  - {result['file']}: {result['error']}")
    
    print(f"\nResults saved to: {output_dir}")
    print(f"{'='*60}")

def save_results(results, output_dir):
    """Save results to JSON file."""
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results_file = os.path.join(output_dir, f"results_{timestamp}.json")
    
    # Convert results to serializable format
    serializable_results = []
    for result in results:
        serializable_result = {
            'file': result['file'],
            'success': result['success'],
            'error': result['error'],
            'verification_output': result.get('verification_output', ''),
            'nr_atoms': result.get('nr_atoms', 0),
            'nr_spec': result.get('nr_spec', 0),
            'timestamp': timestamp
        }
        serializable_results.append(serializable_result)
    
    with open(results_file, 'w') as f:
        json.dump(serializable_results, f, indent=2)
    
    return results_file

def generate_csv_results(results, output_dir, input_dir=None, debug_mode=False):
    """Generate CSV file with filename, result, nr_iterations, spec_link, impl_link, and debug_link columns."""
    csv_file = os.path.join(output_dir, "results.csv")

    # Get repo info
    repo_url = get_git_remote_url()
    branch = get_current_branch() or "main"
    repo_root = get_repo_root()

    with open(csv_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(['filename', 'result', 'nr_iterations', 'spec_link', 'impl_link', 'debug_link'])
        # Write results
        for result in results:
            filename = os.path.basename(result['file'])
            result_status = 'success' if result['success'] else 'failed'
            nr_iterations = result.get('iterations', 1)
            
            # Compute links using robust path calculation
            # For spec files: get the actual path relative to repo root
            if input_dir:
                spec_file_path = Path(input_dir).resolve() / filename
            else:
                spec_file_path = Path(result['file']).resolve()
            rel_spec_path = get_github_path(spec_file_path, repo_root)
            
            # For impl files: get path relative to repo root
            if result.get('output_file'):
                impl_path = Path(result['output_file']).resolve()
                rel_impl_path = get_github_path(impl_path, repo_root)
            else:
                rel_impl_path = ''
            
            # For debug folder: get path relative to repo root (only if debug mode is enabled)
            if debug_mode:
                base_file_name = os.path.splitext(filename)[0]
                debug_folder_path = Path(output_dir).resolve() / "debug" / base_file_name
                rel_debug_path = get_github_path(debug_folder_path, repo_root)
                rel_debug_path_str = str(rel_debug_path).replace('\\', '/')
                debug_link = get_github_url(rel_debug_path_str, repo_url, branch) if repo_url else 'none'
            else:
                debug_link = ''
            
            # Normalize paths and ensure they're strings
            rel_spec_path_str = str(rel_spec_path).replace('\\', '/')
            rel_impl_path_str = str(rel_impl_path).replace('\\', '/') if rel_impl_path else ''
            
            spec_link = get_github_url(rel_spec_path_str, repo_url, branch) if repo_url else 'none'
            impl_link = get_github_url(rel_impl_path_str, repo_url, branch) if repo_url and rel_impl_path_str else 'none'
            writer.writerow([filename, result_status, nr_iterations, spec_link, impl_link, debug_link])
    print(f"CSV results saved to: {csv_file}")
    return csv_file

def generate_summary(results, output_dir, options):
    """Generate a summary of the processing results."""
    successful = [r for r in results if r["success"]]
    failed = [r for r in results if not r["success"]]

    summary_lines = [
        "=== VERICODE DAFNY PROCESSING SUMMARY ===",
        "",
        f"Test directory: {options.get('input_dir', 'unknown')}",
        f"Output directory: {output_dir}",
        f"Test date: {datetime.now().isoformat()}",
        "",
        f"Total original files: {len(results)}",
        "",
        "=== OVERALL STATISTICS ===",
        f"Total successful: {len(successful)}",
        f"Total failed: {len(failed)}",
        f"Success rate: {(len(successful) / len(results) * 100) if results else 0.0:.1f}%",
        "",
        "=== SUCCESSFUL FILES (VERIFIED) ===",
    ]
    
    for result in successful:
        output_file = os.path.basename(result.get("output_file", "no output"))
        summary_lines.append(f"✓ {result['file']} -> {output_file}")

    summary_lines.extend([
        "",
        "=== FAILED FILES (VERIFICATION) ===",
    ])
    
    for result in failed:
        summary_lines.append(f"✗ {result['file']}: {result.get('error', 'unknown error')}")

    summary_lines.extend([
        "",
        "=== CONFIGURATION ===",
        f"Model: {options.get('model', 'unknown')}",
        f"Strict atoms: {options.get('strict_atoms', True)}",
        f"Strict specs: {options.get('strict_specs', True)}",
        f"Debug mode: {'Enabled' if options.get('debug', False) else 'Disabled'}",
        f"Max retries: {options.get('max_retries', 3)}",
        f"Max iterations: {options.get('iterations', 1)}",
        f"Timeout: {options.get('timeout', 120)}s",
        "",
        "=== OUTPUT FILES ===",
        "- All generated implementations saved as impl_*.dfy",
        "- Debug files saved in debug/ subdirectory (if debug mode enabled)",
        "- Results summary saved as summary.txt",
        "- Detailed results saved as results.csv",
        "",
        f"Generated on: {datetime.now().isoformat()}"
    ])

    summary = "\n".join(summary_lines)
    
    summary_file = os.path.join(output_dir, "summary.txt")
    with open(summary_file, "w") as f:
        f.write(summary)
    
    print(f"Summary saved to: {summary_file}")
    return summary

def print_file_result(result, verbose=False):
    """Print result for a single file."""
    if result['success']:
        print(f"✅ {result['file']}")
        if verbose:
            print(f"   ATOMs: {result.get('nr_atoms', 0)}, SPECs: {result.get('nr_spec', 0)}")
            if result.get('iterations'):
                print(f"   Iterations: {result.get('iterations')}")
    else:
        print(f"❌ {result['file']}: {result['error']}")
        if verbose and result.get('verification_output'):
            print(f"   Output: {result['verification_output'][:200]}...")
        if verbose and result.get('iterations'):
            print(f"   Iterations: {result.get('iterations')}")

def print_help():
    """Print help information."""
    help_text = """
Vericode Dafny - AI-powered Dafny code generation and verification

Usage: python vericoder.py [OPTIONS] <directory>

Options:
  -h, --help              Show this help message
  -v, --verbose           Verbose output
  --strict-atoms          Strict verification of ATOM blocks (default: enabled)
  --relaxed-atoms         Relaxed verification of ATOM blocks
  --strict-specs          Strict verification of specifications (default: enabled)
  --relaxed-specs         Relaxed verification of specifications
  --output-dir DIR        Output directory for results (default: input_dir/vericoding_on_YYYY-MM-DD)
  --max-retries N         Maximum number of retries per file (default: 3)
  --timeout N             Timeout in seconds for API calls (default: 120)
  --api-delay N           Delay between API calls in seconds (default: 2.0)
  --model MODEL           LLM model to use (default: claude-sonnet-4-20250514)
  --api-key KEY           API key (or set ANTHROPIC_API_KEY/OPENAI_API_KEY env vars)
  --temperature T         Temperature for LLM generation (default: 0.1)
  --max-tokens N          Maximum tokens for LLM response (default: 8192)
  --iterations N          Maximum verification attempts per file (default: 1)
  --debug                 Enable debug mode (save intermediate files)

Examples:
  python vericoder.py ./benchmarks/bignum_specs/
  python vericoder.py --verbose --output-dir ./results ./benchmarks/
  python vericoder.py --strict-atoms --relaxed-specs ./test_files/
  python vericoder.py --model gpt-4o ./specs/
  python vericoder.py --iterations 3 --debug ./test_files/

Environment Variables:
  ANTHROPIC_API_KEY       Anthropic API key (for Claude)
  OPENAI_API_KEY          OpenAI API key (for OpenAI)
  DAFNY_PATH              Path to Dafny executable (default: dafny)

The tool processes Dafny files containing ATOM and SPEC blocks:
- ATOM blocks: Pre-implemented code that should be preserved exactly
- SPEC blocks: Specifications that should be implemented

Generated code is verified using Dafny and results are saved to the output directory.
"""
    print(help_text)

def format_verification_output(output):
    """Format verification output for display."""
    if not output:
        return "No output"
    
    # Truncate long output
    if len(output) > 500:
        return output[:500] + "..."
    
    return output

def create_output_directory(output_dir):
    """Create output directory if it doesn't exist. If it exists, create a new one with timestamp suffix."""
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
        print(f"Created output directory: {output_dir}")
    else:
        # If directory exists, create a new one with timestamp suffix
        from datetime import datetime
        timestamp = datetime.now().strftime("%H%M%S")
        base_dir = output_dir.rstrip('/')
        new_output_dir = f"{base_dir}_{timestamp}"
        
        # Keep trying with different timestamps if needed
        counter = 1
        while os.path.exists(new_output_dir):
            new_output_dir = f"{base_dir}_{timestamp}_{counter:02d}"
            counter += 1
        
        os.makedirs(new_output_dir)
        print(f"Output directory already exists. Created new directory: {new_output_dir}")
        return new_output_dir
    
    return output_dir

def print_processing_header(directory, options):
    """Print header with processing information."""
    print(f"{'='*60}")
    print(f"VERICODE DAFNY")
    print(f"{'='*60}")
    print(f"Processing directory: {directory}")
    print(f"Output directory: {options.get('output_dir', './output')}")
    model = options.get('model', 'claude-sonnet-4-20250514')
    api_type = 'claude' if model.startswith(('claude-', 'claude')) else 'openai'
    print(f"API type: {api_type}")
    print(f"Model: {model}")
    print(f"Strict atoms: {options.get('strict_atoms', True)}")
    print(f"Strict specs: {options.get('strict_specs', True)}")
    print(f"Max retries: {options.get('max_retries', 3)}")
    print(f"Max iterations: {options.get('iterations', 1)}")
    print(f"Timeout: {options.get('timeout', 120)}s")
    print(f"API delay: {options.get('api_delay', 2.0)}s")
    print(f"Temperature: {options.get('temperature', 0.1)}")
    print(f"{'='*60}")
    print()

def print_retry_info(file_path, attempt, max_retries, error):
    """Print retry information."""
    print(f"  🔄 Retry {attempt}/{max_retries} for {file_path}")
    print(f"     Error: {error}")

def print_verification_result(result):
    """Print detailed verification result."""
    if result['success']:
        print(f"  ✅ Verification successful")
    else:
        print(f"  ❌ Verification failed: {result['error']}")
        if result.get('output'):
            print(f"     Output: {format_verification_output(result['output'])}")

def print_block_verification(block_type, success, details=""):
    """Print block verification result."""
    if success:
        print(f"  ✅ {block_type} blocks preserved")
    else:
        print(f"  ❌ {block_type} blocks modified")
        if details:
            print(f"     {details}")

def print_merge_info(original_specs, generated_impls):
    """Print information about spec-implementation merging."""
    print(f"  📋 Merging {len(original_specs)} specifications with {len(generated_impls)} implementations")
    
    # Count different types of merges
    successful_merges = 0
    empty_merges = 0
    no_impl_found = 0
    
    for spec in original_specs:
        spec_signature = None
        for line in spec.split('\n'):
            if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
                spec_signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
                break
        
        if spec_signature:
            impl_found = False
            for impl in generated_impls:
                impl_signature = None
                for line in impl.split('\n'):
                    if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
                        impl_signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
                        break
                
                if impl_signature == spec_signature:
                    impl_found = True
                    # Check if implementation has a non-empty body
                    impl_body = impl.split('{', 1)[1].split('}', 1)[0] if '{' in impl and '}' in impl else ""
                    impl_body = impl_body.strip()
                    
                    if impl_body and impl_body != "":
                        successful_merges += 1
                    else:
                        empty_merges += 1
                    break
            
            if not impl_found:
                no_impl_found += 1
    
    # Print detailed merge information
    if successful_merges > 0:
        print(f"  ✅ {successful_merges} specifications with non-empty implementations")
    if empty_merges > 0:
        print(f"  ⚠️  {empty_merges} specifications with empty implementations")
    if no_impl_found > 0:
        print(f"  ❌ {no_impl_found} specifications with no implementation found")
    
    total_processed = successful_merges + empty_merges + no_impl_found
    if total_processed > 0:
        print(f"  📊 Total: {total_processed} specifications processed") 