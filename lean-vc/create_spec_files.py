#!/usr/bin/env python3
import os
import re
import glob

def extract_spec_content(file_path):
    """Extract problem_spec, implementation signature, and correctness theorem from a problem file."""
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Extract problem_spec definition
    spec_match = re.search(r'def problem_spec\s*\n(.*?)(?=\n-- end_def problem_spec)', content, re.DOTALL)
    if not spec_match:
        return None
    
    problem_spec = spec_match.group(1).strip()
    
    # Extract implementation signature
    impl_match = re.search(r'def implementation\s*\([^)]*\)\s*:\s*[^:]*:=\s*\n-- end_def implementation_signature', content, re.DOTALL)
    if not impl_match:
        # Try alternative pattern
        impl_match = re.search(r'def implementation\s*\([^)]*\)\s*:\s*[^:]*:=\s*\n-- start_def implementation', content, re.DOTALL)
    
    if impl_match:
        impl_start = impl_match.start()
        impl_end = content.find('-- end_def implementation_signature', impl_start)
        if impl_end == -1:
            impl_end = content.find('-- start_def implementation', impl_start)
        implementation_sig = content[impl_start:impl_end].strip()
    else:
        # Fallback: just get the signature line
        impl_sig_match = re.search(r'def implementation\s*\([^)]*\)\s*:\s*[^:]*:=\s*', content)
        if impl_sig_match:
            implementation_sig = impl_sig_match.group(0).strip()
        else:
            return None
    
    # Extract correctness theorem
    correctness_match = re.search(r'theorem correctness\s*\n(.*?)(?=\n-- end_def correctness_definition)', content, re.DOTALL)
    if not correctness_match:
        return None
    
    correctness = correctness_match.group(1).strip()
    
    return {
        'problem_spec': problem_spec,
        'implementation': implementation_sig,
        'correctness': correctness
    }

def create_spec_file(problem_file, spec_content):
    """Create a spec file with the extracted content."""
    spec_file = problem_file.replace('.lean', '_spec.lean')
    
    # Format the content
    content = f"""def problem_spec
{spec_content['problem_spec']}

def implementation {spec_content['implementation'].replace('def implementation ', '')} sorry

theorem correctness
{spec_content['correctness']} := sorry
"""
    
    with open(spec_file, 'w') as f:
        f.write(content)
    
    print(f"Created: {spec_file}")

def main():
    # Get all problem files that don't already have spec files
    problem_files = glob.glob('benchmarks/clever_specs/problem_*.lean')
    problem_files = [f for f in problem_files if not f.endswith('_spec.lean')]
    
    # Sort by problem number
    def get_problem_number(filename):
        match = re.search(r'problem_(\d+)\.lean', filename)
        return int(match.group(1)) if match else 0
    
    problem_files.sort(key=get_problem_number)
    
    print(f"Processing {len(problem_files)} files...")
    
    for problem_file in problem_files:
        print(f"Processing {problem_file}...")
        spec_content = extract_spec_content(problem_file)
        
        if spec_content:
            create_spec_file(problem_file, spec_content)
        else:
            print(f"  Warning: Could not extract spec content from {problem_file}")

if __name__ == "__main__":
    main() 