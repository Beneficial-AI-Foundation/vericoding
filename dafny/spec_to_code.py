import os
import sys
import json
import requests
import re
import subprocess
import argparse
import csv
from datetime import datetime
from prompt_loader import PromptLoader
from pathlib import Path
from urllib.parse import quote

# Configuration variables
DAFNY_FILES_DIR = ""
MAX_ITERATIONS = 2
OUTPUT_DIR = ""
SUMMARY_FILE = ""
DEBUG_MODE = False
STRICT_ATOM_VERIFICATION = False  # New configuration variable

# Environment variables
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
DAFNY_PATH = os.getenv("DAFNY_PATH", "dafny")

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
        description="Dafny Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python spec_to_code.py
  python spec_to_code.py --dir ./specs --iterations 3
  python spec_to_code.py --dir ./test --debug --iterations 5
  python spec_to_code.py -d ./specs -i 10 --debug
        """
    )
    
    parser.add_argument(
        '--dir', '-d',
        type=str,
        help='Directory with .dfy specification files (default: ./specs)'
    )
    
    parser.add_argument(
        '--iterations', '-i',
        type=int,
        help='Max verification attempts per file (default: 5)'
    )
    
    parser.add_argument(
        '--debug',
        action='store_true',
        help='Enable debug mode (save intermediate files)'
    )
    
    parser.add_argument(
        '--no-prompt',
        action='store_true',
        help='Skip interactive prompts and use command-line arguments only'
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
    global DAFNY_FILES_DIR, MAX_ITERATIONS, OUTPUT_DIR, SUMMARY_FILE, DEBUG_MODE, STRICT_ATOM_VERIFICATION

    print("=== Dafny Specification-to-Code Processing Configuration ===\n")

    # Use command-line arguments if provided
    if args and args.dir:
        DAFNY_FILES_DIR = args.dir
    else:
        # Get directory path
        default_dir = os.path.join(os.getcwd(), "specs")
        DAFNY_FILES_DIR = ask_question(f"Enter directory with .dfy specification files", default_dir)

    if not os.path.isdir(DAFNY_FILES_DIR):
        print(f"Error: Directory '{DAFNY_FILES_DIR}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")
    OUTPUT_DIR = os.path.join(DAFNY_FILES_DIR, f"code_from_spec_on_{timestamp}")
    SUMMARY_FILE = os.path.join(OUTPUT_DIR, "summary.txt")

    os.makedirs(OUTPUT_DIR, exist_ok=True)
    print(f"Created output directory: {OUTPUT_DIR}")

    # Use command-line arguments if provided
    if args and args.iterations:
        MAX_ITERATIONS = args.iterations
    else:
        # Get number of iterations
        iter_input = ask_question("Max verification attempts per file", "5")
        MAX_ITERATIONS = int(iter_input)

    if MAX_ITERATIONS < 1 or MAX_ITERATIONS > 50:
        print("Warning: Number of iterations should be between 1 and 50. Using default value of 5.")
        MAX_ITERATIONS = 5

    # Use command-line arguments if provided
    if args and args.debug:
        DEBUG_MODE = True
    elif args and args.no_prompt:
        DEBUG_MODE = False
    elif args:
        # If other args are provided but not debug, default to False
        DEBUG_MODE = False
    else:
        # Get debug mode setting only if no args provided
        debug_input = ask_question("Enable debug mode (save intermediate files)? (y/N)", "N")
        DEBUG_MODE = debug_input.lower() in ["y", "yes"]

    # Use command-line arguments if provided
    if args and args.strict_atoms:
        STRICT_ATOM_VERIFICATION = True
    elif args and args.no_prompt:
        STRICT_ATOM_VERIFICATION = False  # Default to non-strict
    elif args:
        # If other args are provided but not strict_atoms, default to False
        STRICT_ATOM_VERIFICATION = False
    else:
        # Get strict atoms setting only if no args provided
        strict_atoms_input = ask_question("Enable strict ATOM block verification? (y/N)", "N")
        STRICT_ATOM_VERIFICATION = strict_atoms_input.lower() in ["y", "yes"]

    print("\nConfiguration:")
    print(f"- Directory: {DAFNY_FILES_DIR}")
    print(f"- Output directory: {OUTPUT_DIR}")
    print(f"- Max iterations: {MAX_ITERATIONS}")
    print(f"- Dafny path: {DAFNY_PATH}")
    print(f"- Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print("- Enhanced prompting: Uses hints in method bodies for better code generation")
    print(f"- ATOM block verification: {'Strict' if STRICT_ATOM_VERIFICATION else 'Relaxed (default)'}")
    if DEBUG_MODE:
        print("- DEBUG MODE: Saves code after each iteration to separate files")
    else:
        print("- NORMAL MODE: Saves only final implementation files")

    # Skip confirmation if --no-prompt is used
    if args and args.no_prompt:
        print("\nProceeding with command-line configuration...")
        return

    confirm = ask_question("Proceed with this configuration? (y/N)", "N")
    if confirm.lower() not in ["y", "yes"]:
        print("Operation cancelled by user.")
        sys.exit(0)

def find_dafny_files(directory):
    try:
        files = os.listdir(directory)
        return [os.path.join(directory, f) for f in files if f.endswith(".dfy")]
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

def extract_dafny_code(output):
    """Extract Dafny code from LLM response."""
    # First try to extract from code blocks
    code_block_match = re.search(r'```dafny\n(.*?)```', output, re.DOTALL | re.IGNORECASE)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(code)
        return code
    
    # If no code block, try to find Dafny code patterns
    lines = output.split('\n')
    dafny_lines = []
    in_code = False
    
    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (line.strip().startswith('Looking at') or
            line.strip().startswith('The errors show that:') or
            line.strip().startswith('The issue is in') or
            line.strip().startswith('This function will be') or
            line.strip().startswith('Below is a Dafny program') or
            line.strip().startswith('Theo note:') or
            line.strip().startswith('// This function will be') or
            line.strip().startswith('// Below is a Dafny program') or
            line.strip().startswith('// Theo note:') or
            line.strip().startswith('```') or
            line.strip().startswith('1.') or
            line.strip().startswith('2.') or
            line.strip().startswith('3.') or
            line.strip().startswith('4.') or
            line.strip().startswith('5.')):
            continue
        
        # Start collecting when we see Dafny keywords, block markers, or comment structures
        if (line.find('method ') != -1 or 
            line.find('function ') != -1 or 
            line.find('lemma ') != -1 or 
            line.find('predicate ') != -1 or
            line.find('opaque ') != -1 or
            line.find('ghost ') != -1 or
            line.find('requires ') != -1 or
            line.find('ensures ') != -1 or
            line.find('invariant ') != -1 or
            line.find('decreases ') != -1 or
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
            dafny_lines.append(line)
    
    if dafny_lines:
        code = '\n'.join(dafny_lines).strip()
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
    
    for i, line in enumerate(lines):
        # Track block type
        if line.strip().startswith('//ATOM'):
            in_block = 'ATOM'
        elif line.strip().startswith('//SPEC'):
            in_block = 'SPEC'
        elif line.strip().startswith('//IMPL'):
            in_block = 'IMPL'
        
        # Fix incomplete string literals
        if ':= "' in line and '";' not in line:
            if line.strip().endswith(':= "') or line.strip().endswith(':= ""'):
                line = re.sub(r':= ""?$', ':= "";', line)
            elif line.strip().endswith('"'):
                line = line + ';'
        
        # Fix incomplete variable declarations
        if 'var ' in line and ' := ' in line and not line.endswith(';'):
            if line.strip().endswith(':= ""'):
                line = line + ';'
            elif line.strip().endswith(':= "') or line.strip().endswith(':='):
                line = re.sub(r':= ""?$', ':= "";', line)
        
        # Fix incomplete method bodies
        if line.strip().startswith('method ') and '{' not in line:
            # Look ahead to see if there's a method body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        # Fix incomplete function bodies
        if line.strip().startswith('function ') and '{' not in line:
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function ') or lines[j].strip().startswith('lemma '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        # Fix incomplete lemma bodies
        if line.strip().startswith('lemma ') and '{' not in line:
            # Look ahead to see if there's a lemma body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function ') or lines[j].strip().startswith('lemma '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def save_iteration_code(base_file_name, iteration, code, phase):
    """Save code after each iteration for debugging."""
    # Only save intermediate files if debug mode is enabled
    if not DEBUG_MODE:
        return
    
    if phase == "original":
        # Save original specification
        iteration_file_name = f"{base_file_name}_iter_{iteration}_{phase}.dfy"
    elif phase == "generated":
        # Save initial generated code
        iteration_file_name = f"{base_file_name}_iter_{iteration}_{phase}.dfy"
    elif phase == "current":
        # Save current working version for this iteration
        iteration_file_name = f"{base_file_name}_iter_{iteration}_current.dfy"
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
        "resolution/type errors",
        "parse error", 
        "type error",
        "compilation error",
        "syntax error",
        "method call is not allowed to be used in an expression context",
        "expression is not allowed to invoke a method",
        "cannot resolve",
        "unresolved identifier",
        "invalid unaryexpression",
        "invalid expression",
        "invalid statement",
        "invalid declaration",
        "invalid function",
        "invalid method",
        "invalid lemma",
        "invalid predicate",
        "invalid requires",
        "invalid ensures",
        "invalid invariant",
        "invalid decreases",
        "invalid reads",
        "invalid modifies",
        "invalid frame",
        "invalid ghost",
        "invalid opaque",
        "invalid export",
        "invalid import",
        "invalid include",
        "invalid module",
        "invalid class",
        "invalid trait",
        "invalid datatype",
        "invalid codatatype",
        "invalid newtype",
        "invalid type",
        "invalid variable",
        "invalid constant",
        "invalid field",
        "invalid parameter",
        "invalid return",
        "invalid assignment",
        "invalid call",
        "invalid access",
        "invalid index",
        "invalid member",
        "invalid operator",
        "invalid literal",
        "invalid identifier",
        "invalid token",
        "invalid character",
        "invalid number",
        "invalid string",
        "invalid comment",
        "invalid whitespace",
        "invalid newline",
        "invalid end of file",
        "unexpected token",
        "unexpected character",
        "unexpected end of file",
        "missing token",
        "missing character",
        "missing semicolon",
        "missing brace",
        "missing parenthesis",
        "missing bracket",
        "missing colon",
        "missing equals",
        "missing arrow",
        "missing dot",
        "missing comma",
        "missing space",
        "missing newline",
        "missing end of file",
        "duplicate declaration",
        "duplicate definition",
        "duplicate identifier",
        "duplicate name",
        "duplicate symbol",
        "duplicate token",
        "duplicate character",
        "duplicate whitespace",
        "duplicate newline",
        "duplicate end of file",
        "undefined identifier",
        "undefined name",
        "undefined symbol",
        "undefined token",
        "undefined character",
        "undefined whitespace",
        "undefined newline",
        "undefined end of file",
        "redeclaration",
        "redefinition",
        "redeclaration of",
        "redefinition of",
        "already declared",
        "already defined",
        "already exists",
        "already present",
        "already used",
        "already assigned",
        "already initialized",
        "already called",
        "already accessed",
        "already indexed",
        "already member",
        "already operator",
        "already literal",
        "already identifier",
        "already token",
        "already character",
        "already number",
        "already string",
        "already comment",
        "already whitespace",
        "already newline",
        "already end of file"
    ]
    
    return any(indicator in output.lower() for indicator in compilation_error_indicators)

def verify_dafny_file(file_path):
    """Verify a Dafny file and return the result."""
    try:
        result = subprocess.run([DAFNY_PATH, "verify", file_path], 
                              capture_output=True, text=True, timeout=60)
        full_output = result.stdout + result.stderr
        
        # Check for success indicators
        success_indicators = [
            "Dafny program verifier finished with 0 errors",
            "Dafny program verifier finished with 0 verification conditions",
            "Dafny program verifier finished with 0 VC",
            "Dafny program verifier finished with 0 proof obligations",
            "Dafny program verifier finished with 0 PO"
        ]
        
        # Check for success indicators
        success = any(indicator in full_output for indicator in success_indicators)
        
        # Check for timeouts specifically
        timeout_match = re.search(r"Dafny program verifier finished with (\d+) verified, (\d+) errors, (\d+) time outs", full_output)
        has_timeouts = False
        if timeout_match:
            timeouts = int(timeout_match.group(3))
            has_timeouts = timeouts > 0
        
        # Also check for the pattern "X verified, 0 errors" which is success ONLY if no timeouts
        verified_match = re.search(r"Dafny program verifier finished with (\d+) verified, 0 errors", full_output)
        if verified_match and not has_timeouts:
            success = True
        
        if success:
            return {"success": True, "output": full_output, "error": None}
        else:
            # Extract error count for reporting
            error_count_match = re.search(r"Dafny program verifier finished with (\d+) errors?", full_output)
            if error_count_match:
                error_count = error_count_match.group(1)
                error_msg = f"Verification failed with {error_count} errors"
            else:
                error_msg = "Verification failed"
            
            return {"success": False, "output": full_output, "error": error_msg}
    
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

        base_file_name = os.path.basename(file_path).replace(".dfy", "")

        # Save original code
        save_iteration_code(base_file_name, 0, original_code, "original")

        # Check if original file has compilation errors
        print("  Checking original file for compilation errors...")
        original_verification = verify_dafny_file(file_path)
        
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
        generated_code = extract_dafny_code(generated_response)

        # Verify that all ATOM blocks are preserved
        if STRICT_ATOM_VERIFICATION and not verify_atom_blocks(original_code, generated_code):
            print("  ⚠️  Warning: ATOM blocks were modified. Restoring original ATOM blocks...")
            generated_code = restore_atom_blocks(original_code, generated_code)

        # Save initial generated code
        save_iteration_code(base_file_name, 1, generated_code, "generated")

        # Create output file path
        output_path = os.path.join(OUTPUT_DIR, f"{base_file_name}_impl.dfy")
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
            verification = verify_dafny_file(output_path)
            last_verification = verification

            if verification["success"]:
                print(f"  ✓ Success: {os.path.basename(file_path)}")
                success = True
                break
            else:
                print(f"  ✗ Verification failed: {verification['error']}")
                # Print a snippet of the verification output for debugging
                if verification["output"]:
                    output_lines = verification["output"].split('\n')
                    # Show last few lines of output
                    last_lines = output_lines[-5:] if len(output_lines) > 5 else output_lines
                    print(f"    Verification output (last {len(last_lines)} lines):")
                    for line in last_lines:
                        if line.strip():
                            print(f"      {line.strip()}")
                print(f"    Attempting fix...")

            # Try to fix issues (both compilation and verification errors)
            error_details = verification["error"] or "Unknown error"
            fix_prompt = prompt_loader.format_prompt(
                "fix_verification",
                code=current_code,
                errorDetails=error_details,
                iteration=str(iteration)
            )
            fix_response = call_claude_api(fix_prompt)
            fixed_code = extract_dafny_code(fix_response)

            # Verify that all ATOM blocks are preserved after fix
            if STRICT_ATOM_VERIFICATION and not verify_atom_blocks(original_code, fixed_code):
                print("  ⚠️  Warning: ATOM blocks were modified during fix. Restoring original ATOM blocks...")
                fixed_code = restore_atom_blocks(original_code, fixed_code)

            current_code = fixed_code

        if success:
            print(f"✓ Success: {os.path.basename(file_path)}")
            return {
                "success": True,
                "file": os.path.basename(file_path),
                "error": None,
                "output": output_path,
                "has_bypass": False
            }
        else:
            error_msg = last_verification["error"] if last_verification else f"Failed after {MAX_ITERATIONS} iterations"
            print(f"✗ Failed: {os.path.basename(file_path)} - {error_msg}")
                
            return {
                "success": False,
                "file": os.path.basename(file_path),
                "error": error_msg,
                "output": output_path,
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
            # More lenient check: look for key identifiers (method/function/lemma names)
            identifiers = re.findall(r'(method|function|lemma|predicate)\s+(\w+)', atom_content)
            if identifiers:
                # Check if at least one identifier is preserved
                found_identifier = False
                for decl_type, name in identifiers:
                    if f"{decl_type} {name}" in generated_code:
                        found_identifier = True
                        break
                
                if not found_identifier:
                    return False
            else:
                # If no clear identifiers, be more strict
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
            # Find the corresponding SPEC by matching method/function/lemma signature
            for orig_type, orig_content in original_blocks:
                if orig_type.startswith('SPEC') and get_signature(orig_content) == get_signature(content):
                    impl_map[orig_content.strip()] = content.strip()
                    break
    
    # Reconstruct the code preserving order and ATOM blocks
    result = []
    for block_type, content in original_blocks:
        content = content.strip()
        if block_type == 'ATOM':
            result.extend(['//ATOM', content])
        elif block_type.startswith('SPEC'):
            if content in impl_map:
                # Use the same spec name if present
                spec_name = re.search(r'//SPEC\s+\[([^\]]+)\]', block_type)
                if spec_name:
                    result.extend([f'//IMPL [{spec_name.group(1)}]', impl_map[content]])
                else:
                    result.extend(['//IMPL', impl_map[content]])
            else:
                result.extend([block_type, content])
    
    return '\n\n'.join(result)

def get_signature(code):
    """Extract method/function/lemma signature from code block."""
    lines = code.split('\n')
    for line in lines:
        if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
            # Return the line up to the first { or requires/ensures
            signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
            return signature
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
            spec_name = result['file']
            if result['success']:
                spec_to_code = 'success'
            else:
                spec_to_code = 'failed'
            
            # Compute links - always include dafny/ prefix since files are in dafny subdirectory
            # For spec files: dafny/benchmarks/bignum_specs/test/filename.dfy
            rel_spec_path = Path("dafny") / DAFNY_FILES_DIR / spec_name
            
            # For impl files: dafny/benchmarks/bignum_specs/test/code_from_spec_on_.../filename_impl.dfy
            if result['output']:
                impl_path = Path(result['output'])
                # The impl_path is already the full path, we just need to make it relative to repo root
                # and ensure it has the dafny/ prefix
                try:
                    # Try to get relative path from repo root
                    rel_impl_path = impl_path.relative_to(repo_root)
                except ValueError:
                    # If that fails, construct it manually using the output directory structure
                    rel_impl_path = Path("dafny") / DAFNY_FILES_DIR / impl_path.name
            else:
                rel_impl_path = ''
            
            # Normalize paths and ensure they're strings
            rel_spec_path_str = str(rel_spec_path).replace('\\', '/')
            rel_impl_path_str = str(rel_impl_path).replace('\\', '/') if rel_impl_path else ''
            
            spec_link = get_github_url(rel_spec_path_str, repo_url, branch) if repo_url else ''
            impl_link = get_github_url(rel_impl_path_str, repo_url, branch) if repo_url and rel_impl_path_str else ''
            writer.writerow([spec_name, spec_to_code, spec_link, impl_link])
    print(f"CSV results saved to: {csv_file}")
    return csv_file

def generate_summary(results):
    """Generate a summary of the processing results."""
    successful = [r for r in results if r["success"]]
    failed = [r for r in results if not r["success"]]

    summary_lines = [
        "=== DAFNY SPECIFICATION-TO-CODE PROCESSING SUMMARY (DEBUG VERSION) ===",
        "",
        f"Test directory: {DAFNY_FILES_DIR}",
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
            "- Saves original specification as *_iter_0_original.dfy",
            "- Saves initial generated code as *_iter_1_generated.dfy",
            "- Saves current working version for each iteration as *_iter_N_current.dfy",
            "- Saves final implementation as *_impl.dfy",
            "- Full debugging: all intermediate files are saved",
        ])
    else:
        summary_lines.extend([
            "- Saves only final implementation as *_impl.dfy",
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
    
    print("Starting specification-to-code processing of Dafny files (DEBUG VERSION)...")
    print(f"Directory: {DAFNY_FILES_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print(f"Dafny path: {DAFNY_PATH}")
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
        print("Please set it with: export ANTHROPIC_API_KEY=\"your-api-key\"")
        sys.exit(1)
    
    # Find all Dafny files
    dafny_files = find_dafny_files(DAFNY_FILES_DIR)
    print(f"Found {len(dafny_files)} Dafny files to process")
    print("")

    if not dafny_files:
        print("No Dafny files found. Exiting.")
        return

    # Process each file
    results = []

    for file_path in dafny_files:
        result = process_spec_file(file_path)
        results.append(result)

        # Small delay between files to avoid rate limiting
        import time
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
