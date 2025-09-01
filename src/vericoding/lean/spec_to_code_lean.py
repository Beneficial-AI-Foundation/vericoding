# Lean version of spec_to_code.py, auto-generated for Lean workflow.
import os
import sys
import json
import requests
import re
import subprocess
import argparse
import csv
from datetime import datetime
from vericoding.lean.prompt_loader import PromptLoader
from pathlib import Path
from urllib.parse import quote

# Configuration variables
LEAN_FILES_DIR = ""
MAX_ITERATIONS = 2
OUTPUT_DIR = ""
DEBUG_DIR = ""  # New: debug files directory
SUMMARY_FILE = ""
DEBUG_MODE = False
STRICT_ATOM_VERIFICATION = False  # New configuration variable

# Environment variables
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
LEAN_PATH = os.getenv("LEAN_PATH", "lean")

# Initialize prompt loader (always use prompts-lean.yaml)
try:
    prompt_loader = PromptLoader(prompts_file=Path(__file__).parent / "prompts-lean.yaml")
    # Validate prompts on startup
    validation = prompt_loader.validate_prompts()
    if not validation["valid"]:
        print(f"Warning: Missing required prompts: {', '.join(validation['missing'])}")
        print(f"Available prompts: {', '.join(validation['available'])}")
        sys.exit(1)
except FileNotFoundError as e:
    print(f"Error: {e}")
    print("Please ensure the prompts-lean.yaml file exists with the required prompt files.")
    sys.exit(1)

def parse_arguments():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Lean Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python spec_to_code_lean.py ./NumpySpec/DafnySpecs
  python spec_to_code_lean.py ./NumpySpec/DafnySpecs --iterations 3
  python spec_to_code_lean.py ./NumpySpec/DafnySpecs --debug --iterations 5
  python spec_to_code_lean.py ./NumpySpec/DafnySpecs --iterations 10 --debug
        """
    )
    
    parser.add_argument(
        'folder',
        type=str,
        help='Directory with .lean specification files'
    )
    
    parser.add_argument(
        '--iterations', '-i',
        type=int,
        default=5,
        help='Max verification attempts per file (default: 5)'
    )
    
    parser.add_argument(
        '--debug',
        action='store_true',
        help='Enable debug mode (save intermediate files)'
    )
    
    parser.add_argument(
        '--strict-atoms',
        action='store_true',
        help='Enable strict ATOM block verification (default: relaxed verification)'
    )
    
    parser.add_argument(
        '--timeout',
        type=int,
        default=120,
        help='API timeout in seconds (default: 120)'
    )
    
    parser.add_argument(
        '--output-dir',
        type=str,
        help='Custom output directory (default: auto-generated timestamped directory)'
    )
    
    parser.add_argument(
        '--api-delay',
        type=float,
        default=2.0,
        help='Delay between API calls in seconds (default: 2.0)'
    )
    
    return parser.parse_args()

def ask_question(question, default=None):
    answer = input(f"{question} [{default}]: ")
    return answer.strip() or default

def setup_configuration(args=None):
    global LEAN_FILES_DIR, MAX_ITERATIONS, OUTPUT_DIR, DEBUG_DIR, SUMMARY_FILE, DEBUG_MODE, STRICT_ATOM_VERIFICATION

    print("=== Lean Specification-to-Code Processing Configuration ===\n")

    # Use command-line arguments (with defaults)
    LEAN_FILES_DIR = args.folder

    if not os.path.isdir(LEAN_FILES_DIR):
        print(f"Error: Directory '{LEAN_FILES_DIR}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")
    process_id = os.getpid()
    default_output_dir = os.path.join(LEAN_FILES_DIR, f"vericoder_lean_{timestamp}_pid{process_id}")
    OUTPUT_DIR = args.output_dir or default_output_dir
    DEBUG_DIR = os.path.join(OUTPUT_DIR, "debug")  # Debug files subdirectory
    SUMMARY_FILE = os.path.join(OUTPUT_DIR, "summary.txt")

    os.makedirs(OUTPUT_DIR, exist_ok=True)
    print(f"Created output directory: {OUTPUT_DIR}")
    
    # Create debug directory if debug mode is enabled
    if args.debug:
        os.makedirs(DEBUG_DIR, exist_ok=True)
        print(f"Created debug directory: {DEBUG_DIR}")

    # Use command-line arguments (with defaults)
    MAX_ITERATIONS = args.iterations
    DEBUG_MODE = args.debug
    STRICT_ATOM_VERIFICATION = args.strict_atoms
    API_TIMEOUT = args.timeout
    API_DELAY = args.api_delay

    print("\nConfiguration:")
    print(f"- Directory: {LEAN_FILES_DIR}")
    print(f"- Output directory: {OUTPUT_DIR}")
    if DEBUG_MODE:
        print(f"- Debug directory: {DEBUG_DIR}")
    print(f"- Max iterations: {MAX_ITERATIONS}")
    print(f"- API timeout: {API_TIMEOUT} seconds")
    print(f"- API delay: {API_DELAY} seconds")
    print(f"- Lean path: {LEAN_PATH}")
    print(f"- Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print(f"- ATOM block verification: {'Strict' if STRICT_ATOM_VERIFICATION else 'Relaxed (default)'}")
    if DEBUG_MODE:
        print("- DEBUG MODE: Saves code after each iteration to separate files")
    else:
        print("- NORMAL MODE: Saves only final implementation files")
    print("\nProceeding with configuration...")
    
    return API_TIMEOUT, API_DELAY

def find_lean_files_with_sorry(directory):
    try:
        files = os.listdir(directory)
        lean_files = [os.path.join(directory, f) for f in files if f.endswith(".lean")]
        files_with_sorry = []
        for file in lean_files:
            with open(file, 'r', encoding='utf-8') as f:
                if 'sorry' in f.read():
                    files_with_sorry.append(file)
        return files_with_sorry
    except Exception as e:
        print(f"Error reading directory {directory}: {e}")
        return []

def call_claude_api(prompt, max_retries=3, timeout=120):
    if not ANTHROPIC_API_KEY:
        raise ValueError("ANTHROPIC_API_KEY environment variable is required")

    url = "https://api.anthropic.com/v1/messages"
    headers = {
        "Content-Type": "application/json",
        "x-api-key": ANTHROPIC_API_KEY,
        "anthropic-version": "2023-06-01"
    }
    payload = {
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 8192,
        "messages": [{"role": "user", "content": prompt}]
    }

    for attempt in range(max_retries):
        try:
            response = requests.post(url, headers=headers, json=payload, timeout=timeout)
            response.raise_for_status()
            data = response.json()
            if "content" in data and len(data["content"]) > 0:
                content = data["content"][0]
                if "text" in content:
                    return content["text"]
                else:
                    return str(content)
            else:
                raise ValueError("Unexpected response format from Claude API")
        except requests.exceptions.Timeout:
            print(f"Timeout occurred (attempt {attempt+1}/{max_retries})")
        except Exception as e:
            print(f"Error calling Claude API: {e} (attempt {attempt+1}/{max_retries})")
            # Add exponential backoff for server errors
            if attempt < max_retries - 1:  # Don't sleep after the last attempt
                import time
                sleep_time = (2 ** attempt) * 5  # 5s, 10s, 20s, etc.
                print(f"Waiting {sleep_time} seconds before retry...")
                time.sleep(sleep_time)
    raise RuntimeError("Failed to get response from Claude API after retries")

def extract_lean_code(output):
    """Extract Lean code from LLM output, removing explanations and markdown."""
    
    # Look for code blocks marked with ```lean
    lean_code_pattern = r'```lean\s*\n(.*?)\n```'
    match = re.search(lean_code_pattern, output, re.DOTALL)
    
    if match:
        return match.group(1).strip()
    
    # If no ```lean block found, look for any code block
    code_pattern = r'```\s*\n(.*?)\n```'
    match = re.search(code_pattern, output, re.DOTALL)
    
    if match:
        return match.group(1).strip()
    
    # If no code blocks found, try to extract lines that look like Lean code
    # (containing keywords like def, theorem, namespace, etc.)
    lines = output.split('\n')
    lean_lines = []
    in_code_section = False
    
    for line in lines:
        stripped = line.strip()
        # Skip empty lines and markdown headers
        if not stripped or stripped.startswith('#'):
            continue
        
        # Check if this looks like Lean code
        if any(keyword in stripped for keyword in ['def ', 'theorem ', 'lemma ', 'namespace ', 'end ', 'import ', '/-', '-/', '/--', ':=', 'by', 'intro', 'simp', 'rw', 'exact', 'apply']):
            in_code_section = True
        
        if in_code_section:
            lean_lines.append(line)
    
    if lean_lines:
        return '\n'.join(lean_lines).strip()
    
    # If all else fails, return the original output
    print("Warning: Could not extract Lean code from LLM output, using raw output")
    return output

def save_iteration_code(base_file_name, iteration, code, phase):
    if not DEBUG_MODE:
        return
    # Create a separate subfolder for each file's debug files
    file_debug_dir = os.path.join(DEBUG_DIR, base_file_name)
    os.makedirs(file_debug_dir, exist_ok=True)
    
    file_name = f"iter{iteration}_{phase}.lean"
    file_path = os.path.join(file_debug_dir, file_name)
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(code)

def detect_compilation_errors(output):
    # Look for Lean error messages
    error_patterns = [
        r"error:.*",
        r"failed to elaborate",
        r"unknown identifier",
        r"invalid definition",
        r"unsolved goals",
        r"type mismatch",
        r"unexpected token",
        r"invalid proof"
    ]
    for pattern in error_patterns:
        if re.search(pattern, output, re.IGNORECASE):
            return True
    return False

def verify_lean_file(file_path):
    try:
        result = subprocess.run([LEAN_PATH, file_path], capture_output=True, text=True, timeout=120)
        return result.returncode == 0, result.stdout + '\n' + result.stderr
    except Exception as e:
        return False, str(e)

def process_spec_file(file_path, api_timeout, api_delay):
    base_file_name = os.path.splitext(os.path.basename(file_path))[0]
    print(f"  Reading file: {os.path.basename(file_path)}")
    with open(file_path, 'r', encoding='utf-8') as f:
        code = f.read()

    print(f"  Generating initial code with LLM...")
    prompt = prompt_loader.format_prompt("generate_code", code=code)
    generated_code = call_claude_api(prompt, timeout=api_timeout)
    generated_code = extract_lean_code(generated_code)
    save_iteration_code(base_file_name, 0, generated_code, "initial")
    print(f"  LLM code generated successfully")

    for iteration in range(1, MAX_ITERATIONS + 1):
        print(f"  Iteration {iteration}/{MAX_ITERATIONS}:")
        # Save code for this iteration
        save_iteration_code(base_file_name, iteration, generated_code, "pre_verify")
        # Write code to temp file
        temp_file = os.path.join(OUTPUT_DIR, f"{base_file_name}_temp.lean")
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(generated_code)
        
        print(f"    Performing Lean verification...")
        # Verify with Lean
        verified, output = verify_lean_file(temp_file)
        
        if verified and not detect_compilation_errors(output):
            # Save final code
            final_file = os.path.join(OUTPUT_DIR, f"{base_file_name}_impl.lean")
            with open(final_file, 'w', encoding='utf-8') as f:
                f.write(generated_code)
            print(f"    ✓ Verification successful!")
            print(f"[SUCCESS] {base_file_name} verified after {iteration} iterations.")
            return {
                'success': True,
                'file': os.path.basename(file_path),
                'output': final_file,
                'nr_iter': iteration
            }
        else:
            print(f"    ✗ Verification failed")
            if output.strip():
                print(f"    Error details:")
                # Print first few lines of error output, truncating if too long
                error_lines = output.strip().split('\n')
                for i, line in enumerate(error_lines[:10]):  # Show first 10 lines
                    if line.strip():
                        print(f"      {line}")
                if len(error_lines) > 10:
                    print(f"      ... (truncated, {len(error_lines) - 10} more lines)")
            else:
                print(f"      No error output available")
            
            print(f"    Attempting to fix with LLM...")
            # Prepare error details for next prompt
            error_details = output
            fix_prompt = prompt_loader.format_prompt("fix_verification", code=generated_code, errorDetails=error_details)
            generated_code = call_claude_api(fix_prompt, timeout=api_timeout)
            generated_code = extract_lean_code(generated_code)
            print(f"    LLM fix generated")
    
    # Save last attempt
    final_file = os.path.join(OUTPUT_DIR, f"{base_file_name}_impl.lean")
    with open(final_file, 'w', encoding='utf-8') as f:
        f.write(generated_code)
    print(f"[GAVE UP] {base_file_name} did not verify after {MAX_ITERATIONS} iterations.")
    return {
        'success': False,
        'file': os.path.basename(file_path),
        'output': final_file,
        'nr_iter': MAX_ITERATIONS
    }

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
    if current.name == "lean-vc" and (current.parent / '.git').exists():
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

def generate_csv_results(results):
    """Generate CSV file with filename, result, nr_iterations, spec_link, impl_link, and debug_link columns."""
    csv_file = os.path.join(OUTPUT_DIR, "results.csv")

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
            filename = result['file']
            result_status = 'success' if result['success'] else 'failed'
            nr_iterations = result['nr_iter']
            
            # Compute links using robust path calculation
            # For spec files: get the actual path relative to repo root
            spec_file_path = Path(LEAN_FILES_DIR).resolve() / filename
            rel_spec_path = get_github_path(spec_file_path, repo_root)
            
            # For impl files: get path relative to repo root
            if result['output']:
                impl_path = Path(result['output']).resolve()
                rel_impl_path = get_github_path(impl_path, repo_root)
            else:
                rel_impl_path = ''
            
            # For debug folder: get path relative to repo root (only if debug mode is enabled)
            if DEBUG_MODE:
                base_file_name = os.path.splitext(filename)[0]
                debug_folder_path = Path(DEBUG_DIR).resolve() / base_file_name
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

def main():
    args = parse_arguments()
    api_timeout, api_delay = setup_configuration(args)
    files = find_lean_files_with_sorry(LEAN_FILES_DIR)
    if not files:
        print(f"No .lean files with 'sorry' found in {LEAN_FILES_DIR}")
        sys.exit(0)
    print(f"Found {len(files)} .lean files with 'sorry' in {LEAN_FILES_DIR}")
    results = []
    for i, file_path in enumerate(files, 1):
        print(f"\n[{i}/{len(files)}] Processing {os.path.basename(file_path)} ...")
        result = process_spec_file(file_path, api_timeout, api_delay)
        results.append(result)
    
    # Write summary
    print(f"\n=== Processing Complete ===")
    successful = sum(1 for result in results if result['success'])
    failed = len(results) - successful
    print(f"Successfully processed: {successful}/{len(results)} files")
    print(f"Failed: {failed}/{len(results)} files")
    
    with open(SUMMARY_FILE, 'w', encoding='utf-8') as f:
        for result in results:
            f.write(f"{os.path.basename(result['file'])}: {'SUCCESS' if result['success'] else 'FAILED'}\n")
    print(f"Summary written to {SUMMARY_FILE}")
    
    # Generate CSV results
    csv_file = generate_csv_results(results)
    print(f"CSV results written to {csv_file}")

if __name__ == "__main__":
    main() 