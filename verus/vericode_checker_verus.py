#!/usr/bin/env python3
"""
Vericode Checker Module for Verus
Handles verification, checking, and validation of Verus code.
"""

import os
import re
import subprocess
from vericode_parser_verus import (
    extract_impl_blocks, extract_spec_blocks, extract_todo_blocks,
    extract_specification, extract_body, get_signature, merge_spec_with_body
)

# Environment variables
VERUS_PATH = os.getenv("VERUS_PATH", "verus")
CARGO_PATH = os.getenv("CARGO_PATH", "cargo")

def verify_verus_file(file_path):
    """Verify a Verus file and return the result."""
    try:
        # First, check if we're in a Cargo project
        cargo_toml_dir = find_cargo_toml_dir(file_path)
        if not cargo_toml_dir:
            return {"success": False, "output": "", "error": "No Cargo.toml found in directory tree"}
        
        # Change to the Cargo project directory
        original_dir = os.getcwd()
        os.chdir(cargo_toml_dir)
        
        try:
            # Run cargo check with Verus
            result = subprocess.run([CARGO_PATH, "check"], 
                                  capture_output=True, text=True, timeout=120)
            full_output = result.stdout + result.stderr
            
            # Check for success indicators
            success_indicators = [
                "Finished dev [unoptimized + debuginfo]",
                "0 errors",
                "0 warnings",
                "verification successful",
                "all verification conditions discharged"
            ]
            
            # Check for success
            success = any(indicator in full_output for indicator in success_indicators)
            
            # Check for verification errors specifically
            verification_error_indicators = [
                "verification failed",
                "verification error",
                "postcondition not satisfied",
                "precondition not satisfied",
                "invariant not satisfied",
                "assertion failed",
                "loop invariant not satisfied",
                "decreases clause not satisfied"
            ]
            
            has_verification_errors = any(indicator in full_output.lower() for indicator in verification_error_indicators)
            
            if success and not has_verification_errors:
                return {"success": True, "output": full_output, "error": None}
            else:
                # Extract error information
                error_msg = "Verification failed"
                if has_verification_errors:
                    error_msg = "Verification conditions not satisfied"
                elif "error:" in full_output:
                    error_msg = "Compilation errors found"
                
                return {"success": False, "output": full_output, "error": error_msg}
        
        finally:
            # Restore original directory
            os.chdir(original_dir)
    
    except subprocess.TimeoutExpired:
        return {"success": False, "output": "", "error": "Verification timeout"}
    except Exception as e:
        return {"success": False, "output": "", "error": str(e)}

def find_cargo_toml_dir(file_path):
    """Find the directory containing Cargo.toml by walking up the directory tree."""
    current_dir = os.path.dirname(os.path.abspath(file_path))
    
    while current_dir != os.path.dirname(current_dir):  # Stop at root
        if os.path.exists(os.path.join(current_dir, "Cargo.toml")):
            return current_dir
        current_dir = os.path.dirname(current_dir)
    
    return None

def verify_todo_blocks(original_code, generated_code):
    """Verify that all TODO blocks from the original code are implemented in the generated code."""
    # Extract TODO blocks from original code
    todo_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?:TODO[^{}]*)\s*\}'
    original_todos = re.findall(todo_pattern, original_code, re.DOTALL | re.IGNORECASE)
    
    for todo_func in original_todos:
        # Check if the function is implemented in generated code
        # Look for the function without TODO in the body
        func_pattern = rf'fn\s+{re.escape(todo_func)}\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?!TODO)[^{}]*\}'
        if not re.search(func_pattern, generated_code, re.DOTALL | re.IGNORECASE):
            return False
    
    return True

def verify_specifications(original_code, generated_code):
    """Verify that all specification parts (signatures, ensures, requires) are preserved exactly."""
    # Extract function signatures from original code
    func_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}'
    original_funcs = re.findall(func_pattern, original_code, re.DOTALL)
    
    # Extract function signatures from generated code
    generated_funcs = re.findall(func_pattern, generated_code, re.DOTALL)
    
    # For each original function, find corresponding generated function and verify specification
    for orig_func in original_funcs:
        orig_specification = extract_specification(orig_func)
        orig_signature = get_signature(orig_func)
        
        if not orig_signature:
            continue
        
        # Look for matching implementation
        found_match = False
        for gen_func in generated_funcs:
            gen_signature = get_signature(gen_func)
            
            if gen_signature == orig_signature:
                found_match = True
                gen_specification = extract_specification(gen_func)
                
                # Normalize specifications by removing comments and extra whitespace
                from vericode_parser_verus import normalize_specification
                normalized_orig = normalize_specification(orig_specification)
                normalized_gen = normalize_specification(gen_specification)
                
                if normalized_orig != normalized_gen:
                    print(f"    ⚠️  Specification mismatch for {orig_signature}")
                    print(f"      Original: {normalized_orig}")
                    print(f"      Generated: {normalized_gen}")
                    return False
                break
        
        if not found_match:
            print(f"    ⚠️  No implementation found for specification: {orig_signature}")
            return False
    
    return True

def restore_todo_blocks(original_code, generated_code):
    """Restore original TODO blocks in the generated code, replacing them with implementations."""
    # Extract all functions from original code
    full_func_pattern = r'(fn\s+\w+\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\})'
    original_funcs = re.findall(full_func_pattern, original_code, re.DOTALL)
    
    # Extract all functions from generated code
    generated_funcs = re.findall(full_func_pattern, generated_code, re.DOTALL)
    
    # Create a map of function signatures to their implementations
    impl_map = {}
    for func in generated_funcs:
        signature = get_signature(func)
        if signature:
            impl_map[signature] = func
    
    # Reconstruct the code preserving order and TODO blocks
    result = []
    current_pos = 0
    
    for orig_func in original_funcs:
        orig_signature = get_signature(orig_func)
        
        if orig_signature and orig_signature in impl_map:
            # Use generated implementation
            result.append(impl_map[orig_signature])
        else:
            # Keep original function
            result.append(orig_func)
    
    return '\n\n'.join(result)

def restore_specifications(original_code, generated_code):
    """Restore original specifications in the generated code, keeping only the bodies."""
    # Extract function signatures from original code
    full_func_pattern = r'(fn\s+\w+\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\})'
    original_funcs = re.findall(full_func_pattern, original_code, re.DOTALL)
    
    # Extract function signatures from generated code
    generated_funcs = re.findall(full_func_pattern, generated_code, re.DOTALL)
    
    # Create a map of signatures to bodies
    body_map = {}
    for func in generated_funcs:
        signature = get_signature(func)
        if signature:
            body = extract_body(func)
            body_map[signature] = body
    
    # Reconstruct the code preserving original specifications and generated bodies
    result = []
    for orig_func in original_funcs:
        orig_specification = extract_specification(orig_func)
        orig_signature = get_signature(orig_func)
        
        if orig_signature and orig_signature in body_map:
            # Merge original specification with generated body
            merged_content = merge_spec_with_body(orig_specification, body_map[orig_signature])
            result.append(merged_content)
        else:
            # Keep original if no implementation found
            result.append(orig_func)
    
    return '\n\n'.join(result)

def create_verus_project_structure(output_dir):
    """Create a minimal Verus project structure for verification."""
    # Create Cargo.toml
    cargo_toml_content = '''[package]
name = "vericode-verus-temp"
version = "0.1.0"
edition = "2021"

[dependencies]
vstd = { git = "https://github.com/verus-lang/verus", rev = "9b557d70faab565829c0642c4d56609a44814d82" }
builtin = { git = "https://github.com/verus-lang/verus", rev = "9b557d70faab565829c0642c4d56609a44814d82" }
builtin_macros = { git = "https://github.com/verus-lang/verus", rev = "9b557d70faab565829c0642c4d56609a44814d82" }

[package.metadata.verus]
verify = true
'''
    
    # Create src directory and main.rs
    src_dir = os.path.join(output_dir, "src")
    os.makedirs(src_dir, exist_ok=True)
    
    with open(os.path.join(output_dir, "Cargo.toml"), 'w') as f:
        f.write(cargo_toml_content)
    
    return src_dir

def prepare_verus_file_for_verification(code, output_dir):
    """Prepare a Verus file for verification by creating a proper project structure."""
    # Create project structure
    src_dir = create_verus_project_structure(output_dir)
    
    # Write the code to main.rs
    main_rs_path = os.path.join(src_dir, "main.rs")
    with open(main_rs_path, 'w') as f:
        f.write(code)
    
    return main_rs_path 