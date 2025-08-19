#!/usr/bin/env python3
import os
import re

def extract_impl_blocks(code):
    """Extract IMPL blocks using a flexible regex pattern."""
    pattern = r'//IMPL(?:[ \t]+[^\n]*)?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def show_impl_blocks(file_path):
    """Show IMPL blocks from a single file"""
    print(f"\n{'='*100}")
    print(f"IMPL BLOCKS FROM: {os.path.basename(file_path)}")
    print(f"{'='*100}")
    
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        
        impl_blocks = extract_impl_blocks(content)
        
        if not impl_blocks:
            print("No IMPL blocks found.")
            return
        
        for i, block in enumerate(impl_blocks, 1):
            print(f"\n--- IMPL BLOCK {i} ---")
            print(block.strip())
            print("-" * 80)
                
    except Exception as e:
        print(f"Error processing file: {e}")

def main():
    # Directory containing the generated files
    test_dir = "/Users/sergiu.bursuc/baif/vericoding/dafny/benchmarks/bignum_specs/generated/bignums-full_simple_specs/code_from_spec_on_25-06_12h24_pid23905"
    
    # Get all .dfy files in the directory
    dfy_files = [f for f in os.listdir(test_dir) if f.endswith('.dfy') and 'impl' in f]
    
    print(f"Showing IMPL blocks from {len(dfy_files)} implementation files:")
    for f in dfy_files:
        print(f"  - {f}")
    
    # Show IMPL blocks from each file
    for filename in dfy_files:
        file_path = os.path.join(test_dir, filename)
        show_impl_blocks(file_path)

if __name__ == "__main__":
    main() 