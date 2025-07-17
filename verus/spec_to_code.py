#!/usr/bin/env python3
"""
Verus Specification-to-Code Processing

This script processes Verus specification files containing ATOM and SPEC blocks,
generates implementations using Claude API, and iteratively fixes verification errors.
"""

import os
import sys
import re
import time
import argparse
import requests
import subprocess
import csv
from datetime import datetime
from pathlib import Path
from urllib.parse import quote

# Add the parent directory to Python path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Try to import from dafny directory
try:
    from dafny.prompt_loader import PromptLoader
except ImportError:
    # Fallback: create a simple PromptLoader for verus
    import yaml
    
    class PromptLoader:
        def __init__(self, prompts_file="prompts.yaml"):
            self.prompts_file = prompts_file
            self.prompts = {}
            self._load_prompts()
        
        def _load_prompts(self):
            if os.path.exists(self.prompts_file):
                with open(self.prompts_file, 'r') as f:
                    self.prompts = yaml.safe_load(f)
            else:
                raise FileNotFoundError(f"Prompts file not found: {self.prompts_file}")
        
        def format_prompt(self, prompt_name, **kwargs):
            if prompt_name not in self.prompts:
                raise KeyError(f"Prompt '{prompt_name}' not found")
            return self.prompts[prompt_name].format(**kwargs)
        
        def validate_prompts(self):
            required = ["generate_code", "fix_verification"]
            missing = [p for p in required if p not in self.prompts]
            return {
                "valid": len(missing) == 0,
                "missing": missing,
                "available": list(self.prompts.keys())
            }

# Configuration variables
VERUS_FILES_DIR = ""
MAX_ITERATIONS = 2
OUTPUT_DIR = ""
SUMMARY_FILE = ""
DEBUG_MODE = False
STRICT_ATOM_VERIFICATION = False  # New configuration variable

# Environment variables
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
VERUS_PATH = os.getenv("VERUS_PATH", os.path.expanduser("~/Downloads/verus-0.2025.06.14.9b557d7-x86-linux/verus-x86-linux/verus"))

# Initialize prompt loader
try:
    prompt_loader = PromptLoader()
    # Validate prompts on startup
    validation = prompt_loader.validate_prompts()
    if not validation["valid"]:
        print(f"Warning: Missing required prompts: {', '.join(validation['missing'])}")
        print(f"Available prompts: {', '.join(validation['available'])}")
        sys.exit(1)
except FileNotFoundError as e:
    print(f"Error: {e}")
    print("Please ensure the prompts directory exists with the required prompt files.")
    sys.exit(1)

def parse_arguments():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Verus Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python spec_to_code.py ./specs
  python spec_to_code.py ./benchmarks/verus_specs --iterations 3
  python spec_to_code.py ./test --debug --iterations 5
  python spec_to_code.py ./specs --iterations 10 --debug
        """
    )
    
    parser.add_argument(
        'folder',
        type=str,
        help='Directory with .rs specification files'
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
    
    return parser.parse_args()

def ask_question(question, default=None):
    answer = input(f"{question} [{default}]: ")
    return answer.strip() or default

def setup_configuration(args=None):
    global VERUS_FILES_DIR, MAX_ITERATIONS, OUTPUT_DIR, SUMMARY_FILE, DEBUG_MODE, STRICT_ATOM_VERIFICATION

    print("=== Verus Specification-to-Code Processing Configuration ===\n")

    # Use command-line arguments (with defaults)
    VERUS_FILES_DIR = args.folder

    if not os.path.isdir(VERUS_FILES_DIR):
        print(f"Error: Directory '{VERUS_FILES_DIR}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")
    OUTPUT_DIR = os.path.join(VERUS_FILES_DIR, f"code_from_spec_on_{timestamp}")
    SUMMARY_FILE = os.path.join(OUTPUT_DIR, "summary.txt")

    os.makedirs(OUTPUT_DIR, exist_ok=True)
    print(f"Created output directory: {OUTPUT_DIR}")

    # Use command-line arguments (with defaults)
    MAX_ITERATIONS = args.iterations
    DEBUG_MODE = args.debug
    STRICT_ATOM_VERIFICATION = args.strict_atoms

    print("\nConfiguration:")
    print(f"- Directory: {VERUS_FILES_DIR}")
    print(f"- Output directory: {OUTPUT_DIR}")
    print(f"- Max iterations: {MAX_ITERATIONS}")
    print(f"- Verus path: {VERUS_PATH}")
    print(f"- Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print("- Enhanced prompting: Uses hints in method bodies for better code generation")
    print(f"- ATOM block verification: {'Strict' if STRICT_ATOM_VERIFICATION else 'Relaxed (default)'}")
    if DEBUG_MODE:
        print("- DEBUG MODE: Saves code after each iteration to separate files")
    else:
        print("- NORMAL MODE: Saves only final implementation files")
    print("\nProceeding with configuration...")

def find_verus_files(directory):
    try:
        files = []
        for root, dirs, filenames in os.walk(directory):
            for f in filenames:
                if f.endswith(".rs"):
                    files.append(os.path.join(root, f))
        return files
    except Exception as e:
        print(f"Error reading directory {directory}: {e}")
        return []

def call_claude_api(prompt):
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

    response = requests.post(url, headers=headers, json=payload)
    response.raise_for_status()
    data = response.json()
    
    # Extract text from the response
    if "content" in data and len(data["content"]) > 0:
        content = data["content"][0]
        if "text" in content:
            return content["text"]
        else:
            return str(content)
    else:
        raise ValueError("Unexpected response format from Claude API")

def extract_verus_code(output):
    """Extract Verus code from LLM response."""
    # First try to extract from code blocks
    code_block_match = re.search(r'```rust\n(.*?)```', output, re.DOTALL | re.IGNORECASE)
    if not code_block_match:
        code_block_match = re.search(r'```verus\n(.*?)```', output, re.DOTALL | re.IGNORECASE)
    if not code_block_match:
        code_block_match = re.search(r'```\n(.*?)```', output, re.DOTALL)
    
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(code)
        return code
    
    # If no code block, try to find Verus code patterns
    lines = output.split('\n')
    verus_lines = []
    in_code = False
    
    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (line.strip().startswith('Looking at') or
            line.strip().startswith('The errors show that:') or
            line.strip().startswith('The issue is in') or
            line.strip().startswith('This function will be') or
            line.strip().startswith('Below is a Verus program') or
            line.strip().startswith('Theo note:') or
            line.strip().startswith('// This function will be') or
            line.strip().startswith('// Below is a Verus program') or
            line.strip().startswith('// Theo note:') or
            line.strip().startswith('```') or
            line.strip().startswith('1.') or
            line.strip().startswith('2.') or
            line.strip().startswith('3.') or
            line.strip().startswith('4.') or
            line.strip().startswith('5.')):
            continue
        
        # Start collecting when we see Verus keywords, block markers, or comment structures
        if (line.find('use vstd::') != -1 or
            line.find('use builtin') != -1 or 
            line.find('fn main()') != -1 or
            line.find('verus!') != -1 or
            line.find('fn ') != -1 or 
            line.find('spec fn ') != -1 or 
            line.find('requires') != -1 or
            line.find('ensures') != -1 or
            line.find('invariant') != -1 or
            line.find('decreases') != -1 or
            line.find('proof ') != -1 or
            # Block markers
            line.strip().startswith('//ATOM') or
            line.strip().startswith('//SPEC') or
            line.strip().startswith('//IMPL') or
            # Comment markers
            line.strip().startswith('/* code modified by LLM') or
            line.strip().startswith('// ATOMS') or
            line.strip().startswith('/*') or
            line.strip().startswith('*/')):
            in_code = True
        
        if in_code:
            verus_lines.append(line)
    
    if verus_lines:
        code = '\n'.join(verus_lines).strip()
        code = fix_incomplete_code(code)
        return code
    
    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(code)
    return code

def fix_incomplete_code(code):
    """Fix common incomplete code patterns."""
    lines = code.split('\n')
    fixed_lines = []
    in_block = None  # Track current block type (ATOM, SPEC, or IMPL)
    in_verus_block = False
    
    for i, line in enumerate(lines):
        # Track block type
        if line.strip().startswith('//ATOM'):
            in_block = 'ATOM'
        elif line.strip().startswith('//SPEC'):
            in_block = 'SPEC'
        elif line.strip().startswith('//IMPL'):
            in_block = 'IMPL'
        
        # Track verus! block
        if 'verus!' in line:
            in_verus_block = True
        elif line.strip() == '} // verus!' or line.strip() == '}':
            in_verus_block = False
        
        # Fix incomplete function bodies
        if line.strip().startswith('fn ') and '{' not in line and not line.strip().endswith(';'):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if '{' in lines[j] or lines[j].strip().startswith('unimplemented!') or lines[j].strip().startswith('return'):
                    has_body = True
                    break
                if lines[j].strip().startswith('//') or lines[j].strip().startswith('fn ') or lines[j].strip().startswith('spec fn'):
                    break
            if not has_body and in_block != 'SPEC':
                # Add empty body with TODO comment
                fixed_lines.append(line)
                fixed_lines.append('{')
                fixed_lines.append('    return false;  // TODO: Remove this line and implement the function body')
                fixed_lines.append('}')
                continue
        
        # Fix incomplete spec function bodies
        if line.strip().startswith('spec fn ') and '{' not in line and not line.strip().endswith(';'):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if '{' in lines[j] or lines[j].strip() == ';':
                    has_body = True
                    break
                if lines[j].strip().startswith('//') or lines[j].strip().startswith('fn ') or lines[j].strip().startswith('spec fn'):
                    break
            if not has_body and in_block != 'SPEC':
                # Add semicolon for spec functions without body
                fixed_lines.append(line + ';')
                continue
        
        fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def save_iteration_code(base_file_name, iteration, code, phase):
    """Save code after each iteration for debugging."""
    # Only save intermediate files if debug mode is enabled
    if not DEBUG_MODE:
        return
    
    if phase == "original":
        # Save original specification
        iteration_file_name = f"{base_file_name}_iter_{iteration}_{phase}.rs"
    elif phase == "generated":
        # Save initial generated code
        iteration_file_name = f"{base_file_name}_iter_{iteration}_{phase}.rs"
    elif phase == "current":
        # Save current working version for this iteration
        iteration_file_name = f"{base_file_name}_iter_{iteration}_current.rs"
    else:
        # Skip other phases (before_verify, after_fix, etc.)
        return
    
    iteration_path = os.path.join(OUTPUT_DIR, iteration_file_name)
    with open(iteration_path, "w") as f:
        f.write(code)
    print(f"    💾 Saved {phase} code to: {iteration_file_name}")

def detect_compilation_errors(output):
    """Detect if the output contains compilation errors."""
    compilation_error_indicators = [
        "error:",
        "compilation error",
        "syntax error",
        "parse error", 
        "type error",
        "cannot find",
        "unresolved",
        "undeclared",
        "undefined",
        "mismatched types",
        "expected",
        "found",
        "invalid",
        "unexpected token",
        "unexpected character",
        "missing",
        "duplicate",
        "already defined",
        "conflicting",
        "incompatible"
    ]
    
    return any(indicator in output.lower() for indicator in compilation_error_indicators)

def verify_verus_file(file_path):
    """Verify a Verus file and return the result."""
    try:
        # First try compilation check
        result = subprocess.run([VERUS_PATH, "--no-verify", file_path], 
                              capture_output=True, text=True, timeout=60)
        
        if result.returncode != 0:
            # Compilation failed
            full_output = result.stdout + result.stderr
            return {"success": False, "output": full_output, "error": f"Compilation failed: {full_output}"}
        
        # If compilation succeeded, try verification
        result = subprocess.run([VERUS_PATH, file_path], 
                              capture_output=True, text=True, timeout=120)
        full_output = result.stdout + result.stderr
        
        # Check for success indicators
        if result.returncode == 0:
            return {"success": True, "output": full_output, "error": None}
        else:
            return {"success": False, "output": full_output, "error": f"Verification failed: {full_output}"}
    
    except subprocess.TimeoutExpired:
        return {"success": False, "output": "", "error": "Verification timeout"}
    except Exception as e:
        return {"success": False, "output": "", "error": str(e)}

def process_spec_file(file_path):
    """Process a single specification file."""
    try:
        print(f"Processing: {os.path.basename(file_path)}")

        # Read the original file
        with open(file_path, "r") as f:
            original_code = f.read()

        base_file_name = os.path.basename(file_path).replace(".rs", "")

        # Save original code
        save_iteration_code(base_file_name, 0, original_code, "original")

        # Check if original file has compilation errors
        print("  Checking original file for compilation errors...")
        original_verification = verify_verus_file(file_path)
        
        if not original_verification["success"]:
            print(f"  ⚠️  Original file has issues: {original_verification['error']}")
            print(f"  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications (preserving ATOM blocks and implementing SPEC blocks)
        print("  Step 1: Generating code from specifications...")
        generate_prompt = prompt_loader.format_prompt(
            "generate_code",
            code=original_code
        )
        generated_response = call_claude_api(generate_prompt)
        generated_code = extract_verus_code(generated_response)

        # Verify that all ATOM blocks are preserved
        if STRICT_ATOM_VERIFICATION and not verify_atom_blocks(original_code, generated_code):
            print("  ⚠️  Warning: ATOM blocks were modified. Restoring original ATOM blocks...")
            generated_code = restore_atom_blocks(original_code, generated_code)

        # Save initial generated code
        save_iteration_code(base_file_name, 1, generated_code, "generated")

        # Create output file path
        output_path = os.path.join(OUTPUT_DIR, f"{base_file_name}_impl.rs")
        with open(output_path, "w") as f:
            f.write(generated_code)

        # Run verification iterations
        current_code = generated_code
        success = False
        last_verification = None

        for iteration in range(1, MAX_ITERATIONS + 1):
            print(f"  Iteration {iteration}/{MAX_ITERATIONS}: Verifying...")

            # Write current code to file
            with open(output_path, "w") as f:
                f.write(current_code)

            # Save current working version for this iteration
            save_iteration_code(base_file_name, iteration, current_code, "current")

            # Verify
            verification = verify_verus_file(output_path)
            last_verification = verification

            if verification["success"]:
                print(f"    ✓ Verification successful!")
                success = True
                break
            else:
                print(f"    ✗ Verification failed: {verification['error'][:200]}...")

            # Try to fix issues (both compilation and verification errors)
            error_details = verification["error"] or "Unknown error"

            # Only attempt fix if not on last iteration
            if iteration < MAX_ITERATIONS:
                print(f"    Attempting to fix errors...")
                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    errorDetails=error_details,
                    iteration=iteration
                )
                
                try:
                    fix_response = call_claude_api(fix_prompt)
                    fixed_code = extract_verus_code(fix_response)
                    
                    # Verify that all ATOM blocks are still preserved
                    if STRICT_ATOM_VERIFICATION and not verify_atom_blocks(original_code, fixed_code):
                        print("    ⚠️  Warning: ATOM blocks were modified during fix. Restoring original ATOM blocks...")
                        fixed_code = restore_atom_blocks(original_code, fixed_code)
                    
                    current_code = fixed_code
                    print(f"    Generated fix for iteration {iteration}")
                except Exception as e:
                    print(f"    ✗ Failed to generate fix: {str(e)}")
                    break

        if success:
            print(f"  ✓ Successfully generated and verified: {os.path.basename(output_path)}")
            return {
                "success": True,
                "file": os.path.basename(file_path),
                "output": output_path,
                "error": None,
                "has_bypass": False
            }
        else:
            error_msg = last_verification["error"] if last_verification else "Unknown verification error"
            print(f"  ✗ Failed to verify after {MAX_ITERATIONS} iterations: {error_msg[:200]}...")
            return {
                "success": False,
                "file": os.path.basename(file_path),
                "output": output_path,
                "error": error_msg,
                "has_bypass": False
            }

    except Exception as e:
        print(f"✗ Failed: {os.path.basename(file_path)} - {str(e)}")
        return {
            "success": False,
            "file": os.path.basename(file_path),
            "error": str(e),
            "output": None,
            "has_bypass": False
        }

def verify_atom_blocks(original_code, generated_code):
    """Verify that all ATOM blocks from the original code are preserved in the generated code."""
    # Updated regex to handle new format with spec names and constraints
    original_atoms = re.findall(r'//ATOM\n(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
    for atom in original_atoms:
        atom_content = atom.strip()
        
        # Normalize whitespace for comparison
        normalized_atom = re.sub(r'\s+', ' ', atom_content)
        normalized_generated = re.sub(r'\s+', ' ', generated_code)
        
        # Check if the normalized content is present
        if normalized_atom not in normalized_generated:
            print(f"    ⚠️  ATOM block missing or modified: {atom_content[:100]}...")
            return False
    
    return True

def restore_atom_blocks(original_code, generated_code):
    """Restore original ATOM blocks in the generated code."""
    # Updated regex to handle new format with spec names and constraints
    # Extract all blocks from original code - handle //SPEC [name] and //CONSTRAINTS
    original_blocks = re.findall(r'//(ATOM|SPEC(?:\s+\[[^\]]+\])?)\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
    # Extract all blocks from generated code - handle //IMPL [name] and //CONSTRAINTS
    generated_blocks = re.findall(r'//(ATOM|IMPL(?:\s+\[[^\]]+\])?|SPEC(?:\s+\[[^\]]+\])?)\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|IMPL|SPEC)|$)', generated_code, re.DOTALL)
    
    # Create a map of SPEC blocks to their implementations
    impl_map = {}
    for block_type, content in generated_blocks:
        if block_type.startswith('IMPL'):
            spec_name = block_type.replace('IMPL', 'SPEC')
            impl_map[spec_name] = content.strip()
    
    # Reconstruct the code preserving order and ATOM blocks
    result = []
    for block_type, content in original_blocks:
        content = content.strip()
        if block_type == 'ATOM':
            result.append(f'//{block_type}\n{content}')
        elif block_type.startswith('SPEC'):
            impl_name = block_type.replace('SPEC', 'IMPL')
            if impl_name in impl_map:
                result.append(f'//{impl_name}\n{impl_map[impl_name]}')
            else:
                result.append(f'//{block_type}\n{content}')
    
    return '\n\n'.join(result)

def get_signature(code):
    """Extract function signature from code block."""
    lines = code.split('\n')
    for line in lines:
        if any(keyword in line for keyword in ['pub fn ', 'fn ', 'spec fn ']):
            return line.strip()
    return None

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
            remote_url = remote_url.replace('git@github.com:', 'https://github.com/').replace('.git', '')
        elif remote_url.startswith('https://github.com/'):
            remote_url = remote_url.replace('.git', '')
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
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
            return "main"

def get_github_url(file_path, repo_url, branch="main"):
    repo_url = repo_url.rstrip('/')
    encoded_path = quote(str(file_path))
    github_url = f"{repo_url}/blob/{branch}/{encoded_path}"
    return github_url

def get_repo_root():
    """
    Find the repository root by looking for .git directory.
    Returns:
        Path: Repository root path
    """
    current = Path.cwd()
    while current != current.parent:
        if (current / '.git').exists():
            return current
        current = current.parent
    return Path.cwd()  # Fallback to current directory

def generate_csv_results(results):
    """Generate CSV file with spec_name, spec_to_code, spec_link, and impl_link columns."""
    csv_file = os.path.join(OUTPUT_DIR, "results.csv")

    # Get repo info
    repo_url = get_git_remote_url() or ""
    branch = get_current_branch() or "main"
    repo_root = get_repo_root()

    with open(csv_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(['spec_name', 'spec_to_code', 'spec_link', 'impl_link'])
        # Write results
        for result in results:
            spec_name = result["file"].replace(".rs", "")
            spec_to_code = "SUCCESS" if result["success"] else "FAILED"
            
            # Generate spec link
            spec_rel_path = os.path.relpath(os.path.join(VERUS_FILES_DIR, result["file"]), repo_root)
            spec_link = get_github_url(spec_rel_path, repo_url, branch) if repo_url else ""
            
            # Generate impl link
            if result["output"]:
                impl_rel_path = os.path.relpath(result["output"], repo_root)
                impl_link = get_github_url(impl_rel_path, repo_url, branch) if repo_url else ""
            else:
                impl_link = ""
            
            writer.writerow([spec_name, spec_to_code, spec_link, impl_link])
    
    print(f"CSV results saved to: {csv_file}")
    return csv_file

def generate_summary(results):
    """Generate a summary of the processing results."""
    successful = [r for r in results if r["success"]]
    failed = [r for r in results if not r["success"]]

    summary_lines = [
        "=== VERUS SPECIFICATION-TO-CODE PROCESSING SUMMARY (DEBUG VERSION) ===",
        "",
        f"Test directory: {VERUS_FILES_DIR}",
        f"Output directory: {OUTPUT_DIR}",
        f"Max iterations: {MAX_ITERATIONS}",
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
        output_file = os.path.basename(result["output"]) if result["output"] else "no output"
        summary_lines.append(f"✓ {result['file']} -> {output_file}")

    summary_lines.extend([
        "",
        "=== FAILED FILES (VERIFICATION) ===",
    ])
    
    for result in failed:
        summary_lines.append(f"✗ {result['file']}")

    summary_lines.extend([
        "",
        "=== DEBUG FEATURES ===",
        f"Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}",
    ])
    
    if DEBUG_MODE:
        summary_lines.extend([
            "- Saves original specification as *_iter_0_original.rs",
            "- Saves initial generated code as *_iter_1_generated.rs",
            "- Saves current working version for each iteration as *_iter_N_current.rs",
            "- Saves final implementation as *_impl.rs",
            "- Full debugging: all intermediate files are saved",
        ])
    else:
        summary_lines.extend([
            "- Saves only final implementation as *_impl.rs",
            "- No intermediate files saved (debug mode disabled)",
        ])
    
    summary_lines.extend([
        "",
        f"- Debug mode control: {'Enabled' if DEBUG_MODE else 'Disabled'}",
        "- Configurable file output based on debug setting",
        "",
        f"Generated on: {datetime.now().isoformat()}"
    ])

    summary = "\n".join(summary_lines)
    
    with open(SUMMARY_FILE, "w") as f:
        f.write(summary)
    
    return summary

def main():
    # Parse command-line arguments first
    args = parse_arguments()
    
    # Set up configuration before printing status
    setup_configuration(args)
    
    print("Starting specification-to-code processing of Verus files (DEBUG VERSION)...")
    print(f"Directory: {VERUS_FILES_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print(f"Verus path: {VERUS_PATH}")
    print(f"Max iterations: {MAX_ITERATIONS}")
    print(f"Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print(f"- ATOM block verification: {'Strict' if STRICT_ATOM_VERIFICATION else 'Relaxed (default)'}")
    print("Processing each file by generating code from specifications.")
    print("Enhanced prompting: Uses hints in method bodies for better code generation.")
    if DEBUG_MODE:
        print("DEBUG MODE: Saves code after each iteration to separate files for analysis.")
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    if not ANTHROPIC_API_KEY:
        print("Error: ANTHROPIC_API_KEY environment variable is required")
        print('Please set it with: export ANTHROPIC_API_KEY="your-api-key"')
        sys.exit(1)
    
    # Find all Verus files
    verus_files = find_verus_files(VERUS_FILES_DIR)
    print(f"Found {len(verus_files)} Verus files to process")
    print("")

    if not verus_files:
        print("No Verus files found. Exiting.")
        return

    # Process each file
    results = []

    for file_path in verus_files:
        result = process_spec_file(file_path)
        results.append(result)

        # Small delay between files to avoid rate limiting
        time.sleep(2)

    # Generate summary
    print("")
    print("Generating summary...")
    summary = generate_summary(results)

    print("")
    print("=== SUMMARY ===")
    print(summary)
    print("")
    print(f"Summary saved to: {SUMMARY_FILE}")
    print(f"All generated files saved to: {OUTPUT_DIR}")
    if DEBUG_MODE:
        print("DEBUG: Files saved: original, generated, current per iteration, and final implementation")
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    csv_file = generate_csv_results(results)

if __name__ == "__main__":
    main()
