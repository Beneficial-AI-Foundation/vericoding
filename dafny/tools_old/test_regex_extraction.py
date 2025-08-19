#!/usr/bin/env python3
import os
import re
import sys

def extract_impl_blocks(code):
    """Extract IMPL blocks using a flexible regex pattern."""
    pattern = r'//IMPL(?:[ \t]+[^\n]*)?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_spec_blocks(code):
    """Extract SPEC blocks using the regex pattern from spec_to_code.py"""
    pattern = r'//SPEC(?:\s+\[[^\]]+\])?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_atom_blocks(code):
    """Extract ATOM blocks using the regex pattern from spec_to_code.py"""
    pattern = r'//ATOM\n(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def test_file(file_path):
    """Test the regex extraction on a single file"""
    print(f"\n{'='*80}")
    print(f"Testing file: {os.path.basename(file_path)}")
    print(f"{'='*80}")
    
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Test different block types
        impl_blocks = extract_impl_blocks(content)
        spec_blocks = extract_spec_blocks(content)
        atom_blocks = extract_atom_blocks(content)
        
        print(f"Found {len(impl_blocks)} IMPL blocks:")
        for i, block in enumerate(impl_blocks, 1):
            print(f"\n--- IMPL Block {i} ---")
            show_block_preview(block)
            signature = get_signature(block)
            if signature:
                print(f"Signature: {signature}")
        
        print(f"\nFound {len(spec_blocks)} SPEC blocks:")
        for i, block in enumerate(spec_blocks, 1):
            print(f"\n--- SPEC Block {i} ---")
            show_block_preview(block)
            signature = get_signature(block)
            if signature:
                print(f"Signature: {signature}")
        
        print(f"\nFound {len(atom_blocks)} ATOM blocks:")
        for i, block in enumerate(atom_blocks, 1):
            print(f"\n--- ATOM Block {i} ---")
            show_block_preview(block)
            signature = get_signature(block)
            if signature:
                print(f"Signature: {signature}")
        
        # Also check for any lines containing IMPL, SPEC, or ATOM
        print(f"\n--- Raw Block Markers Found ---")
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if '//IMPL' in line or '//SPEC' in line or '//ATOM' in line:
                print(f"Line {i+1}: {line.strip()}")
                
    except Exception as e:
        print(f"Error processing file: {e}")

def show_block_preview(block):
    """Show a preview of a code block"""
    lines = block.strip().split('\n')
    if len(lines) <= 8:
        print(block.strip())
    else:
        print("First 4 lines:")
        for line in lines[:4]:
            print(f"  {line}")
        print("...")
        print("Last 4 lines:")
        for line in lines[-4:]:
            print(f"  {line}")

def get_signature(code_block):
    """Extract method/function/lemma signature from code block."""
    lines = code_block.split('\n')
    for line in lines:
        if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
            # Return the line up to the first { or requires/ensures
            signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
            return signature
    return None

def main():
    # Directory containing the generated files
    test_dir = "/Users/sergiu.bursuc/baif/vericoding/dafny/benchmarks/bignum_specs/generated/bignums-full_simple_specs/code_from_spec_on_25-06_12h24_pid23905"
    
    # Get all .dfy files in the directory
    dfy_files = [f for f in os.listdir(test_dir) if f.endswith('.dfy') and 'impl' in f]
    
    print(f"Found {len(dfy_files)} implementation files to test:")
    for f in dfy_files:
        print(f"  - {f}")
    
    # Test each file
    for filename in dfy_files:
        file_path = os.path.join(test_dir, filename)
        test_file(file_path)

if __name__ == "__main__":
    main() 