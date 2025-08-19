#!/usr/bin/env python3
"""
Vericode Verus - Main Module
AI-powered Verus code generation and verification tool.
"""

import os
import sys
import argparse
import tempfile
import requests
import time

# Import our modules
from vericode_parser_verus import (
    find_verus_files, extract_verus_code, extract_impl_blocks, 
    extract_spec_blocks, extract_todo_blocks, count_todos_and_specs,
    detect_compilation_errors, preserve_imports
)
from vericode_checker_verus_simple import (
    verify_verus_file, verify_todo_blocks, verify_specifications,
    prepare_verus_file_for_verification
)
from vericode_printer_verus import (
    print_summary, save_results, print_file_result, print_help,
    create_output_directory, print_processing_header, print_retry_info,
    print_verification_result, print_block_verification, print_merge_info
)

# Environment variables
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
VERUS_PATH = os.getenv("VERUS_PATH", "verus")
CARGO_PATH = os.getenv("CARGO_PATH", "cargo")

def load_prompts():
    """Load prompts for Verus code generation."""
    # For now, we'll use simple prompts. In the future, this could load from a YAML file
    prompts = {
        "generate_code": """You are an expert Verus programmer. Given a Verus specification file with TODO comments, implement the missing function bodies.

The input file contains:
- Verus specifications with ensures/requires clauses
- Functions with TODO comments that need implementation
- Spec functions and proof functions that should be preserved

Your task is to:
1. Implement all functions marked with TODO comments
2. Preserve all specifications (ensures/requires clauses) exactly
3. Ensure the code compiles and verifies with Verus
4. Use proper Verus syntax and patterns

Here is the Verus code to implement:

{code}

Please provide the complete Verus code with all TODO functions implemented:""",
        
        "fix_verification": """You are an expert Verus programmer. The following Verus code failed verification with the error:

Error: {errorDetails}

Here is the code that needs to be fixed:

{code}

Please fix the verification errors and provide the corrected Verus code. Ensure all specifications are preserved and the code compiles successfully."""
    }
    return prompts

def call_claude_api(prompt, max_retries=3, timeout=120, temperature=0.1, max_tokens=8192):
    """Call Claude API with the given prompt."""
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
        "max_tokens": max_tokens,
        "temperature": temperature,
        "messages": [{"role": "user", "content": prompt}]
    }

    for attempt in range(max_retries):
        try:
            response = requests.post(url, headers=headers, json=payload, timeout=timeout)
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
        except requests.exceptions.Timeout:
            if attempt < max_retries - 1:
                print(f"    ⚠️  API request timed out, retrying... (attempt {attempt + 1}/{max_retries})")
                continue
            else:
                raise ValueError(f"API request timed out after {timeout} seconds (all retries exhausted)")
        except requests.exceptions.RequestException as e:
            if attempt < max_retries - 1:
                print(f"    ⚠️  API request failed, retrying... (attempt {attempt + 1}/{max_retries}): {str(e)}")
                # Add exponential backoff for server errors
                if hasattr(e, 'response') and e.response and e.response.status_code >= 500:
                    backoff_time = min(2 ** attempt, 30)  # Exponential backoff, max 30 seconds
                    print(f"    ⏳ Server error detected, waiting {backoff_time}s before retry...")
                    time.sleep(backoff_time)
                else:
                    time.sleep(1)  # Short delay for other errors
                continue
            else:
                raise ValueError(f"API request failed after {max_retries} attempts: {str(e)}")
        except Exception as e:
            if attempt < max_retries - 1:
                print(f"    ⚠️  Unexpected error, retrying... (attempt {attempt + 1}/{max_retries}): {str(e)}")
                continue
            else:
                raise ValueError(f"Unexpected error during API call after {max_retries} attempts: {str(e)}")
    
    # This should never be reached, but just in case
    raise ValueError("All API call attempts failed")

def call_openai_api(prompt, model="gpt-4o", temperature=0.1, max_tokens=4000, api_key=None):
    """Call OpenAI API with the given prompt."""
    try:
        import openai
        from openai import OpenAI
    except ImportError:
        raise ValueError("OpenAI package not installed. Run: pip install openai")
    
    if api_key:
        client = OpenAI(api_key=api_key)
    else:
        client = OpenAI()
    
    try:
        response = client.chat.completions.create(
            model=model,
            messages=[{"role": "user", "content": prompt}],
            temperature=temperature,
            max_tokens=max_tokens
        )
        return response.choices[0].message.content
    except Exception as e:
        print(f"Error calling OpenAI API: {e}")
        return None

def detect_api_type(model):
    """Detect API type from model name."""
    if model.startswith(('claude-', 'claude')):
        return 'claude'
    elif model.startswith(('gpt-', 'gpt')):
        return 'openai'
    else:
        # Default to Claude for unknown models
        return 'claude'

def call_api(prompt, model="claude-sonnet-4-20250514", **kwargs):
    """Call the appropriate API based on the model."""
    api_type = detect_api_type(model)
    if api_type == "claude":
        # Extract only the parameters that call_claude_api accepts
        max_retries = kwargs.get('max_retries', 3)
        timeout = kwargs.get('timeout', 120)
        temperature = kwargs.get('temperature', 0.1)
        max_tokens = kwargs.get('max_tokens', 8192)
        return call_claude_api(prompt, max_retries=max_retries, timeout=timeout, 
                              temperature=temperature, max_tokens=max_tokens)
    elif api_type == "openai":
        return call_openai_api(prompt, model=model, **kwargs)
    else:
        raise ValueError(f"Unsupported API type for model: {model}")

def save_debug_file(base_file_name, phase, code, output_dir):
    """Save debug file if debug mode is enabled."""
    debug_dir = os.path.join(output_dir, "debug")
    if not os.path.exists(debug_dir):
        return
    
    # Create a debug subdirectory for this specific file
    file_debug_dir = os.path.join(debug_dir, base_file_name)
    os.makedirs(file_debug_dir, exist_ok=True)
    
    debug_file_name = f"{base_file_name}_{phase}.rs"
    debug_file_path = os.path.join(file_debug_dir, debug_file_name)
    
    with open(debug_file_path, 'w') as f:
        f.write(code)
    
    print(f"    💾 Saved {phase} code to: debug/{base_file_name}/{debug_file_name}")

def process_file(file_path, prompts, options):
    """Process a single Verus file."""
    print(f"Processing {file_path}...")
    
    # Read the original file
    with open(file_path, 'r') as f:
        original_code = f.read()
    
    # Save original code for debug
    base_file_name = os.path.basename(file_path).replace('.rs', '')
    output_dir = options.get('output_dir', './output')
    save_debug_file(base_file_name, "original", original_code, output_dir)
    
    # Count TODOs and SPECs
    nr_todos, nr_spec = count_todos_and_specs(original_code)
    
    # Extract blocks for analysis
    todo_blocks = extract_todo_blocks(original_code)
    spec_blocks = extract_spec_blocks(original_code)
    
    # For Verus files, we consider functions with default return values as the main targets
    if not todo_blocks:
        return {
            'file': file_path,
            'success': False,
            'error': 'No functions with default return values found',
            'nr_todos': nr_todos,
            'nr_spec': nr_spec
        }
    
    # Create the prompt
    try:
        prompt = prompts["generate_code"].format(code=original_code)
    except Exception as e:
        return {
            'file': file_path,
            'success': False,
            'error': f'Failed to format prompt: {str(e)}',
            'nr_todos': nr_todos,
            'nr_spec': nr_spec
        }
    
    # Call API
    max_retries = options.get('max_retries', 3)
    model = options.get('model', 'claude-sonnet-4-20250514')
    api_delay = options.get('api_delay', 2.0)
    
    for attempt in range(max_retries):
        if attempt > 0:
            print_retry_info(file_path, attempt + 1, max_retries, "API call failed")
            time.sleep(api_delay)  # Add delay between retries
        
        try:
            response = call_api(
                prompt,
                model=model,
                timeout=options.get('timeout', 120),
                temperature=options.get('temperature', 0.1),
                max_tokens=options.get('max_tokens', 8192),
                api_key=options.get('api_key')
            )
            
            if response:
                break
        except Exception as e:
            api_type = detect_api_type(model)
            if attempt == max_retries - 1:
                return {
                    'file': file_path,
                    'success': False,
                    'error': f'Failed to get response from {api_type.upper()} API: {str(e)}',
                    'nr_todos': nr_todos,
                    'nr_spec': nr_spec
                }
            continue
    else:
        api_type = detect_api_type(model)
        return {
            'file': file_path,
            'success': False,
            'error': f'Failed to get response from {api_type.upper()} API after {max_retries} attempts',
            'nr_todos': nr_todos,
            'nr_spec': nr_spec
        }
    
    # Extract Verus code from response
    generated_code = extract_verus_code(response)
    
    # Save generated code for debug
    save_debug_file(base_file_name, "generated", generated_code, output_dir)
    
    if not generated_code:
        return {
            'file': file_path,
            'success': False,
            'error': 'No Verus code found in response',
            'nr_todos': nr_todos,
            'nr_spec': nr_spec
        }
    
    # Check for compilation errors in the response
    if detect_compilation_errors(response):
        return {
            'file': file_path,
            'success': False,
            'error': 'Compilation errors detected in response',
            'nr_todos': nr_todos,
            'nr_spec': nr_spec
        }
    
    # Preserve imports from original code
    generated_code = preserve_imports(original_code, generated_code)
    
    # Verify TODO blocks if strict mode is enabled
    strict_todos = options.get('strict_todos', True)
    if strict_todos and todo_blocks:
        todos_implemented = verify_todo_blocks(original_code, generated_code)
        if not todos_implemented:
            print_block_verification("TODO", False, "TODO blocks were not implemented")
        else:
            print_block_verification("TODO", True)
    
    # Handle specifications
    strict_specs = options.get('strict_specs', True)
    if strict_specs and spec_blocks:
        # Verify specifications are preserved
        specs_preserved = verify_specifications(original_code, generated_code)
        if not specs_preserved:
            print_block_verification("SPEC", False, "Specifications were modified")
        else:
            print_block_verification("SPEC", True)
        
        # Extract generated implementations for info
        generated_impls = extract_impl_blocks(generated_code)
        if spec_blocks:
            print_merge_info(spec_blocks, generated_impls)
        else:
            print(f"  📋 Found {len(todo_blocks)} functions with default return values to implement")
    
    # Save final processed code for debug
    save_debug_file(base_file_name, "final", generated_code, output_dir)
    
    # Run verification iterations
    current_code = generated_code
    success = False
    last_verification = None
    final_iteration = 0
    max_iterations = options.get('iterations', 1)
    
    for iteration in range(1, max_iterations + 1):
        print(f"  Iteration {iteration}/{max_iterations}: Verifying...")
        
        # Create a temporary directory for verification
        with tempfile.TemporaryDirectory() as temp_dir:
            try:
                # Prepare the file for verification
                main_rs_path = prepare_verus_file_for_verification(current_code, temp_dir)
                
                # Save current working version for this iteration
                save_debug_file(base_file_name, f"iter_{iteration}", current_code, output_dir)
                
                # Verify the generated code
                verification_result = verify_verus_file(main_rs_path)
                last_verification = verification_result
                
                if verification_result['success']:
                    print(f"  ✓ Success: {os.path.basename(file_path)}")
                    success = True
                    final_iteration = iteration
                    break
                else:
                    print(f"  ✗ Verification failed: {verification_result['error']}")
                    # Print a snippet of the verification output for debugging
                    if verification_result["output"]:
                        output_lines = verification_result["output"].split('\n')
                        # Show last few lines of output
                        last_lines = output_lines[-5:] if len(output_lines) > 5 else output_lines
                        print(f"    Verification output (last {len(last_lines)} lines):")
                        for line in last_lines:
                            if line.strip():
                                print(f"      {line.strip()}")
                    
                    if iteration < max_iterations:
                        print(f"    Attempting fix...")
                        
                        # Try to fix issues using the fix_verification prompt
                        error_details = verification_result["error"] or "Unknown error"
                        try:
                            fix_prompt = prompts["fix_verification"].format(
                                code=current_code,
                                errorDetails=error_details
                            )
                            print(f"    Calling API for fix attempt {iteration}...")
                            fix_response = call_api(
                                fix_prompt,
                                model=options.get('model', 'claude-sonnet-4-20250514'),
                                timeout=options.get('timeout', 120),
                                temperature=options.get('temperature', 0.1),
                                max_tokens=options.get('max_tokens', 8192),
                                api_key=options.get('api_key')
                            )
                            print(f"    ✓ Fix attempt {iteration} completed")
                            fixed_code = extract_verus_code(fix_response)
                            
                            if fixed_code:
                                current_code = fixed_code
                            else:
                                print(f"    ⚠️  No valid code in fix response, continuing with current code...")
                        except Exception as e:
                            print(f"    ✗ Failed to fix code: {str(e)}")
                            print(f"    ⚠️  Continuing with current code for next iteration...")
                            continue
                    else:
                        print(f"    Max iterations reached, stopping...")
            
            except Exception as e:
                print(f"    ✗ Error during verification: {str(e)}")
                if iteration < max_iterations:
                    continue
                else:
                    break
    
    # If we didn't succeed, set final_iteration to max_iterations
    if not success:
        final_iteration = max_iterations
    
    # Always save the final implementation (both successful and failed)
    output_dir = options.get('output_dir', './output')
    
    filename = os.path.basename(file_path)
    output_file = os.path.join(output_dir, f"impl_{filename}")
    
    with open(output_file, 'w') as f:
        f.write(current_code)
    
    if success:
        return {
            'file': file_path,
            'success': True,
            'error': None,
            'verification_output': last_verification['output'],
            'nr_todos': nr_todos,
            'nr_spec': nr_spec,
            'output_file': output_file,
            'iterations': final_iteration
        }
    else:
        error_msg = last_verification["error"] if last_verification else f"Failed after {max_iterations} iterations"
        return {
            'file': file_path,
            'success': False,
            'error': error_msg,
            'verification_output': last_verification['output'] if last_verification else None,
            'nr_todos': nr_todos,
            'nr_spec': nr_spec,
            'output_file': output_file,
            'iterations': final_iteration
        }

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description='AI-powered Verus code generation and verification')
    parser.add_argument('directory', help='Directory containing Verus files to process')
    parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    parser.add_argument('--strict-todos', action='store_true', default=True, help='Strict verification of TODO blocks (default: enabled)')
    parser.add_argument('--relaxed-todos', action='store_true', help='Relaxed verification of TODO blocks')
    parser.add_argument('--strict-specs', action='store_true', default=True, help='Strict verification of specifications (default: enabled)')
    parser.add_argument('--relaxed-specs', action='store_true', help='Relaxed verification of specifications')
    parser.add_argument('--output-dir', help='Output directory for results (default: input_dir/vericoding_on_YYYY-MM-DD)')
    parser.add_argument('--max-retries', type=int, default=3, help='Maximum number of retries per file (default: 3)')
    parser.add_argument('--timeout', type=int, default=120, help='Timeout in seconds for API calls (default: 120)')
    parser.add_argument('--api-delay', type=float, default=2.0, help='Delay between API calls in seconds (default: 2.0)')
    parser.add_argument('--model', default='claude-sonnet-4-20250514', help='LLM model to use (default: claude-sonnet-4-20250514)')
    parser.add_argument('--api-key', help='API key (or set ANTHROPIC_API_KEY/OPENAI_API_KEY env vars)')
    parser.add_argument('--temperature', type=float, default=0.1, help='Temperature for LLM generation (default: 0.1)')
    parser.add_argument('--max-tokens', type=int, default=8192, help='Maximum tokens for LLM response (default: 8192)')
    parser.add_argument('--iterations', type=int, default=1, help='Maximum verification attempts per file (default: 1)')
    parser.add_argument('--debug', action='store_true', help='Enable debug mode (save intermediate files)')
    
    args = parser.parse_args()
    
    # Handle help
    if len(sys.argv) == 1 or '-h' in sys.argv or '--help' in sys.argv:
        print_help()
        return
    
    # Handle relaxed options
    if args.relaxed_todos:
        args.strict_todos = False
    if args.relaxed_specs:
        args.strict_specs = False
    
    # Check if directory exists
    if not os.path.exists(args.directory):
        print(f"Error: Directory {args.directory} does not exist")
        sys.exit(1)
    
    # Check API key availability based on model
    api_type = detect_api_type(args.model)
    if api_type == 'claude' and not ANTHROPIC_API_KEY and not args.api_key:
        print("Error: ANTHROPIC_API_KEY environment variable or --api-key is required for Claude")
        sys.exit(1)
    elif api_type == 'openai' and not OPENAI_API_KEY and not args.api_key:
        print("Error: OPENAI_API_KEY environment variable or --api-key is required for OpenAI")
        sys.exit(1)
    
    # Load prompts
    prompts = load_prompts()
    
    # Create output directory as subfolder of input directory
    if args.output_dir:
        # Use custom output directory if specified
        output_dir = args.output_dir
    else:
        # Create default output directory as subfolder of input directory
        from datetime import datetime
        current_date = datetime.now().strftime("%Y-%m-%d")
        output_dir = os.path.join(args.directory, f"vericoding_on_{current_date}")
    
    output_dir = create_output_directory(output_dir)
    
    # Create debug directory if debug mode is enabled
    if args.debug:
        debug_dir = os.path.join(output_dir, "debug")
        os.makedirs(debug_dir, exist_ok=True)
        print(f"Debug mode enabled. Debug files will be saved to: {debug_dir}")
    
    # Prepare options
    api_type = detect_api_type(args.model)
    options = {
        'strict_todos': args.strict_todos,
        'strict_specs': args.strict_specs,
        'output_dir': output_dir,
        'debug': args.debug,
        'max_retries': args.max_retries,
        'timeout': args.timeout,
        'api_delay': args.api_delay,
        'model': args.model,
        'api_key': args.api_key or (ANTHROPIC_API_KEY if api_type == 'claude' else OPENAI_API_KEY),
        'temperature': args.temperature,
        'max_tokens': args.max_tokens,
        'iterations': args.iterations
    }
    
    # Print processing header
    print_processing_header(args.directory, options)
    
    # Find Verus files
    verus_files = find_verus_files(args.directory)
    
    if not verus_files:
        print(f"No Verus files found in {args.directory}")
        return
    
    print(f"Found {len(verus_files)} Verus files")
    print()
    
    # Process files
    results = []
    for file_path in verus_files:
        result = process_file(file_path, prompts, options)
        results.append(result)
        
        if args.verbose:
            print_file_result(result, verbose=True)
        else:
            print_file_result(result, verbose=False)
        print()
        
        # Add delay between files
        if len(verus_files) > 1:
            time.sleep(options['api_delay'])
    
    # Print summary and save results
    print_summary(results, output_dir)
    save_results(results, output_dir)
    
    # Generate summary.txt and results.csv files
    from vericode_printer_verus import generate_summary, generate_csv_results
    options['input_dir'] = args.directory
    generate_summary(results, output_dir, options)
    generate_csv_results(results, output_dir, input_dir=args.directory, debug_mode=args.debug)

if __name__ == "__main__":
    main() 