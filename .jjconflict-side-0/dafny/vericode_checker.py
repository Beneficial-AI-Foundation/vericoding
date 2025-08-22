#!/usr/bin/env python3
"""
Vericode Checker Module
Handles verification, checking, and validation of Dafny code.
"""

import os
import re
import subprocess
from vericode_parser import (
    extract_impl_blocks, extract_spec_blocks, extract_atom_blocks,
    extract_specification, extract_body, get_signature, merge_spec_with_body
)

# Environment variables
DAFNY_PATH = os.getenv("DAFNY_PATH", "dafny")

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

def verify_atom_blocks(original_code, generated_code):
    """Verify that all ATOM blocks from the original code are preserved in the generated code."""
    # Updated regex to handle new format with spec names and constraints
    original_atoms = re.findall(r'//\s*ATOM\n(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
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

def verify_specifications(original_code, generated_code):
    """Verify that all specification parts (signatures, requires, ensures) are preserved exactly."""
    # Extract SPEC blocks from original code
    original_specs = re.findall(r'//\s*SPEC(?:\s+\[[^\]]+\])?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
    # Extract IMPL blocks from generated code
    generated_impls = re.findall(r'//\s*IMPL[^\n]*\n([\s\S]*?)(?=//(?:ATOM|SPEC|IMPL)|$)', generated_code, re.DOTALL)
    
    # For each original spec, find corresponding impl and verify specification
    for orig_spec in original_specs:
        orig_spec = orig_spec.strip()
        orig_specification = extract_specification(orig_spec)
        
        # Find corresponding implementation by matching signature
        orig_signature = get_signature(orig_spec)
        if not orig_signature:
            continue
        
        # Look for matching implementation
        found_match = False
        for gen_impl in generated_impls:
            gen_impl = gen_impl.strip()
            gen_signature = get_signature(gen_impl)
            
            if gen_signature == orig_signature:
                found_match = True
                gen_specification = extract_specification(gen_impl)
                
                # Normalize specifications by removing comments and extra whitespace
                from vericode_parser import normalize_specification
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

def restore_atom_blocks(original_code, generated_code):
    """Restore original ATOM blocks in the generated code."""
    # Updated regex to handle new format with spec names and constraints
    # Extract all blocks from original code - handle //SPEC [name] and //CONSTRAINTS
    original_blocks = re.findall(r'//(ATOM|SPEC(?:\s+\[[^\]]+\])?)\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
    # Extract all blocks from generated code - handle //IMPL [name] and //CONSTRAINTS
    generated_blocks = re.findall(r'//(ATOM|IMPL(?:\s+\[[^\]]+\])?|SPEC(?:\s+\[[^\]]+\])?)\n(?://CONSTRAINTS:[^\n]*\n)?([\s\S]*?)(?=//(?:ATOM|IMPL|SPEC)|$)', generated_code, re.DOTALL)
    
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

def restore_specifications(original_code, generated_code):
    """Restore original specifications in the generated code, keeping only the bodies."""
    # Extract SPEC blocks from original code
    original_blocks = re.findall(r'//(ATOM|SPEC(?:\s+\[[^\]]+\])?)\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)', original_code, re.DOTALL)
    
    # Extract IMPL blocks from generated code
    generated_blocks = re.findall(r'//\s*IMPL[^\n]*\n([\s\S]*?)(?=//(?:ATOM|SPEC|IMPL)|$)', generated_code, re.DOTALL)
    
    # Create a map of signatures to bodies
    body_map = {}
    for block in generated_blocks:
        signature = get_signature(block)
        if signature:
            body = extract_body(block)
            body_map[signature] = body
    
    # Reconstruct the code preserving original specifications and generated bodies
    result = []
    for block_type, content in original_blocks:
        content = content.strip()
        if block_type == 'ATOM':
            result.extend(['//ATOM', content])
        elif block_type.startswith('SPEC'):
            # Get the spec name if present
            spec_name_match = re.search(r'//SPEC\s+\[([^\]]+)\]', block_type)
            spec_name = spec_name_match.group(1) if spec_name_match else None
            
            # Extract original specification
            orig_specification = extract_specification(content)
            orig_signature = get_signature(content)
            
            if orig_signature and orig_signature in body_map:
                # Merge original specification with generated body
                merged_content = merge_spec_with_body(orig_specification, body_map[orig_signature])
                
                if spec_name:
                    result.extend([f'//IMPL [{spec_name}]', merged_content])
                else:
                    result.extend(['//IMPL', merged_content])
            else:
                # Keep original if no implementation found
                result.extend([block_type, content])
    
    return '\n\n'.join(result) 