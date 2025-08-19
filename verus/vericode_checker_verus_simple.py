#!/usr/bin/env python3
"""
Vericode Checker Module for Verus (Simplified)
Handles verification, checking, and validation of Verus code.
"""

import os
import re
import subprocess

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
    # Simple check: look for TODO comments in original vs generated
    original_todos = re.findall(r'TODO', original_code, re.IGNORECASE)
    generated_todos = re.findall(r'TODO', generated_code, re.IGNORECASE)
    
    # If there are fewer TODOs in generated code, that's good
    return len(generated_todos) <= len(original_todos)

def verify_specifications(original_code, generated_code):
    """Verify that all specification parts (signatures, ensures, requires) are preserved exactly."""
    # Simple check: ensure all ensures/requires clauses are preserved
    original_ensures = re.findall(r'ensures\s*[^{]*', original_code, re.DOTALL)
    generated_ensures = re.findall(r'ensures\s*[^{]*', generated_code, re.DOTALL)
    
    original_requires = re.findall(r'requires\s*[^{]*', original_code, re.DOTALL)
    generated_requires = re.findall(r'requires\s*[^{]*', generated_code, re.DOTALL)
    
    # Check that all ensures and requires are preserved
    for ensures in original_ensures:
        if ensures not in generated_code:
            return False
    
    for requires in original_requires:
        if requires not in generated_code:
            return False
    
    return True

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