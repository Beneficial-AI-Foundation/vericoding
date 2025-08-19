#!/usr/bin/env python3
import os
import re

def extract_impl_blocks(code):
    """Extract IMPL blocks using a flexible regex pattern."""
    pattern = r'//IMPL(?:[ \t]+[^\n]*)?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_specification(code_block):
    """Extract the specification part (signature + requires + ensures) from a code block."""
    lines = code_block.split('\n')
    spec_lines = []
    in_body = False
    
    for line in lines:
        stripped = line.strip()
        if stripped == '{':
            in_body = True
            break
        if not in_body:
            spec_lines.append(line)
    
    return '\n'.join(spec_lines).strip()

def extract_body(code_block):
    """Extract the body part from a code block."""
    lines = code_block.split('\n')
    body_lines = []
    in_body = False
    brace_count = 0
    
    for line in lines:
        stripped = line.strip()
        if stripped == '{':
            in_body = True
            brace_count += 1
            body_lines.append(line)
        elif in_body:
            body_lines.append(line)
            if stripped == '{':
                brace_count += 1
            elif stripped == '}':
                brace_count -= 1
                if brace_count == 0:
                    break
    
    return '\n'.join(body_lines).strip()

def get_signature(code_block):
    """Extract method/function/lemma signature from code block."""
    lines = code_block.split('\n')
    for line in lines:
        if any(keyword in line for keyword in ['method ', 'function ', 'lemma ']):
            # Return the line up to the first { or requires/ensures
            signature = line.split('{')[0].split('requires')[0].split('ensures')[0].strip()
            return signature
    return None

def show_spec_and_body(file_path):
    """Show specification and body separation for IMPL blocks."""
    print(f"\n{'='*100}")
    print(f"SPEC vs BODY: {os.path.basename(file_path)}")
    print(f"{'='*100}")
    
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        
        impl_blocks = extract_impl_blocks(content)
        
        if not impl_blocks:
            print("No IMPL blocks found.")
            return
        
        for i, block in enumerate(impl_blocks, 1):
            print(f"\n{'#'*60}")
            print(f"IMPL BLOCK {i}")
            print(f"{'#'*60}")
            
            spec = extract_specification(block)
            body = extract_body(block)
            
            if spec:
                print(f"SPECIFICATION:")
                print(f"{'~'*30}")
                print(spec)
            
            if body:
                print(f"\nIMPLEMENTATION BODY:")
                print(f"{'~'*30}")
                print(body)
            
            print(f"\n{'-'*60}")
                
    except Exception as e:
        print(f"Error: {e}")

def main():
    test_dir = "/Users/sergiu.bursuc/baif/vericoding/dafny/benchmarks/bignum_specs/generated/bignums-full_simple_specs/code_from_spec_on_25-06_12h24_pid23905"
    dfy_files = [f for f in os.listdir(test_dir) if f.endswith('.dfy') and 'impl' in f]
    
    print(f"Separating spec and body for {len(dfy_files)} files")
    
    for filename in dfy_files:
        file_path = os.path.join(test_dir, filename)
        show_spec_and_body(file_path)

if __name__ == "__main__":
    main() 