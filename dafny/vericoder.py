#!/usr/bin/env python3
"""
Vericode Dafny - Main Module
AI-powered Dafny code generation and verification tool.
"""

import os
import sys
import argparse
import tempfile
import requests
import time

# Import our modules
from vericode_parser import (
    find_dafny_files, extract_dafny_code, extract_impl_blocks, 
    extract_spec_blocks, extract_atom_blocks, count_atoms_and_specs,
    detect_compilation_errors
)
from vericode_checker import (
    verify_dafny_file, verify_atom_blocks, verify_specifications,
    restore_atom_blocks, restore_specifications
)
from vericode_printer import (
    print_summary, save_results, print_file_result, print_help,
    create_output_directory, print_processing_header, print_retry_info,
    print_verification_result, print_block_verification, print_merge_info
)

# Import prompt loader from original code
try:
    from prompt_loader import PromptLoader
except ImportError:
    print("Error: prompt_loader.py not found. Please ensure it's in the same directory.")
    sys.exit(1)

# Environment variables
ANTHROPIC_API_KEY = os.getenv("ANTHROPIC_API_KEY")
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY")
DAFNY_PATH = os.getenv("DAFNY_PATH", "dafny")

def load_prompts():
    """Load prompts using the original PromptLoader."""
    try:
        prompt_loader = PromptLoader()
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation["valid"]:
            print(f"Warning: Missing required prompts: {', '.join(validation['missing'])}")
            print(f"Available prompts: {', '.join(validation['available'])}")
            sys.exit(1)
        return prompt_loader
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print("Please ensure the prompts directory exists with the required prompt files.")
        sys.exit(1)

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
    
    debug_file_name = f"{base_file_name}_{phase}.dfy"
    debug_file_path = os.path.join(file_debug_dir, debug_file_name)
    
    with open(debug_file_path, 'w') as f:
        f.write(code)
    
    print(f"    💾 Saved {phase} code to: debug/{base_file_name}/{debug_file_name}")

def process_file(file_path, prompt_loader, options):
    """Process a single Dafny file."""
    print(f"Processing {file_path}...")
    
    # Read the original file
    with open(file_path, 'r') as f:
        original_code = f.read()
    
    # Save original code for debug
    base_file_name = os.path.basename(file_path).replace('.dfy', '')
    output_dir = options.get('output_dir', './output')
    save_debug_file(base_file_name, "original", original_code, output_dir)
    
    # Count ATOMs and SPECs
    nr_atoms, nr_spec = count_atoms_and_specs(original_code)
    
    # Extract blocks for analysis
    atom_blocks = extract_atom_blocks(original_code)
    spec_blocks = extract_spec_blocks(original_code)
    
    if not spec_blocks:
        return {
            'file': file_path,
            'success': False,
            'error': 'No SPEC blocks found',
            'nr_atoms': nr_atoms,
            'nr_spec': nr_spec
        }
    
    # Create the prompt using the original prompt loader
    try:
        prompt = prompt_loader.format_prompt(
            "generate_code",
            code=original_code
        )
    except Exception as e:
        return {
            'file': file_path,
            'success': False,
            'error': f'Failed to format prompt: {str(e)}',
            'nr_atoms': nr_atoms,
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
                    'nr_atoms': nr_atoms,
                    'nr_spec': nr_spec
                }
            continue
    else:
        api_type = detect_api_type(model)
        return {
            'file': file_path,
            'success': False,
            'error': f'Failed to get response from {api_type.upper()} API after {max_retries} attempts',
            'nr_atoms': nr_atoms,
            'nr_spec': nr_spec
        }
    
    # Extract Dafny code from response
    generated_code = extract_dafny_code(response)
    
    # Save generated code for debug
    save_debug_file(base_file_name, "generated", generated_code, output_dir)
    
    if not generated_code:
        return {
            'file': file_path,
            'success': False,
            'error': 'No Dafny code found in response',
            'nr_atoms': nr_atoms,
            'nr_spec': nr_spec
        }
    
    # Check for compilation errors in the response
    if detect_compilation_errors(response):
        return {
            'file': file_path,
            'success': False,
            'error': 'Compilation errors detected in response',
            'nr_atoms': nr_atoms,
            'nr_spec': nr_spec
        }
    
    # Verify ATOM blocks if strict mode is enabled
    strict_atoms = options.get('strict_atoms', True)
    if strict_atoms and atom_blocks:
        atoms_preserved = verify_atom_blocks(original_code, generated_code)
        if not atoms_preserved:
            print_block_verification("ATOM", False, "ATOM blocks were modified")
            # Restore original ATOM blocks
            generated_code = restore_atom_blocks(original_code, generated_code)
        else:
            print_block_verification("ATOM", True)
    
    # Handle specifications
    strict_specs = options.get('strict_specs', True)
    if strict_specs and spec_blocks:
        # Verify specifications are preserved
        specs_preserved = verify_specifications(original_code, generated_code)
        if not specs_preserved:
            print_block_verification("SPEC", False, "Specifications were modified")
            # Restore original specifications with generated bodies
            generated_code = restore_specifications(original_code, generated_code)
        else:
            print_block_verification("SPEC", True)
        
        # Extract generated implementations for info
        generated_impls = extract_impl_blocks(generated_code)
        print_merge_info(spec_blocks, generated_impls)
    
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
        
        # Write current code to a temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.dfy', delete=False) as f:
            f.write(current_code)
            temp_file = f.name
        
        try:
            # Save current working version for this iteration
            save_debug_file(base_file_name, f"iter_{iteration}", current_code, output_dir)
            
            # Verify the generated code
            verification_result = verify_dafny_file(temp_file)
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
                        fix_prompt = prompt_loader.format_prompt(
                            "fix_verification",
                            code=current_code,
                            errorDetails=error_details,
                            iteration=str(iteration)
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
                        fixed_code = extract_dafny_code(fix_response)
                        
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
        
        finally:
            # Clean up temporary file
            try:
                os.unlink(temp_file)
            except:
                pass
    
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
            'nr_atoms': nr_atoms,
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
            'nr_atoms': nr_atoms,
            'nr_spec': nr_spec,
            'output_file': output_file,
            'iterations': final_iteration
        }

def main():
    """Main function."""
    parser = argparse.ArgumentParser(description='AI-powered Dafny code generation and verification')
    parser.add_argument('directory', help='Directory containing Dafny files to process')
    parser.add_argument('-v', '--verbose', action='store_true', help='Verbose output')
    parser.add_argument('--strict-atoms', action='store_true', default=True, help='Strict verification of ATOM blocks (default: enabled)')
    parser.add_argument('--relaxed-atoms', action='store_true', help='Relaxed verification of ATOM blocks')
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
    if args.relaxed_atoms:
        args.strict_atoms = False
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
    prompt_loader = load_prompts()
    
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
        'strict_atoms': args.strict_atoms,
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
    
    # Find Dafny files
    dafny_files = find_dafny_files(args.directory)
    
    if not dafny_files:
        print(f"No .dfy files found in {args.directory}")
        return
    
    print(f"Found {len(dafny_files)} Dafny files")
    print()
    
    # Process files
    results = []
    for file_path in dafny_files:
        result = process_file(file_path, prompt_loader, options)
        results.append(result)
        
        if args.verbose:
            print_file_result(result, verbose=True)
        else:
            print_file_result(result, verbose=False)
        print()
        
        # Add delay between files
        if len(dafny_files) > 1:
            time.sleep(options['api_delay'])
    
    # Print summary and save results
    print_summary(results, output_dir)
    save_results(results, output_dir)
    
    # Generate summary.txt and results.csv files
    from vericode_printer import generate_summary, generate_csv_results
    options['input_dir'] = args.directory
    generate_summary(results, output_dir, options)
    generate_csv_results(results, output_dir, input_dir=args.directory, debug_mode=args.debug)

if __name__ == "__main__":
    main() 