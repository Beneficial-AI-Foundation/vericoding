#!/usr/bin/env python3
import os
import re
from pathlib import Path

def fix_spec_file(file_path):
    """Fix common issues in spec files."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Fix duplicate "def problem_spec" declarations
    # Replace multiple consecutive "def problem_spec" lines with a single one
    content = re.sub(r'def problem_spec\s*\ndef problem_spec', 'def problem_spec', content)
    
    # Fix ":= := sorry" syntax error in theorem declarations
    content = re.sub(r':= := sorry', ':= sorry', content)
    
    # Fix any remaining duplicate "def problem_spec" at the beginning
    lines = content.split('\n')
    fixed_lines = []
    skip_next = False
    
    for i, line in enumerate(lines):
        if skip_next:
            skip_next = False
            continue
            
        if line.strip() == 'def problem_spec' and i + 1 < len(lines) and lines[i + 1].strip() == 'def problem_spec':
            fixed_lines.append(line)
            skip_next = True  # Skip the next duplicate line
        else:
            fixed_lines.append(line)
    
    content = '\n'.join(fixed_lines)
    
    # Write the fixed content back
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    return True  # Assume changes were made if we got here

def main():
    spec_dir = Path("benchmarks/clever_specs")
    
    if not spec_dir.exists():
        print(f"Directory {spec_dir} does not exist!")
        return
    
    spec_files = list(spec_dir.glob("problem_*_spec.lean"))
    print(f"Found {len(spec_files)} spec files to check")
    
    fixed_count = 0
    for spec_file in spec_files:
        print(f"Checking {spec_file.name}...")
        if fix_spec_file(spec_file):
            print(f"  Fixed {spec_file.name}")
            fixed_count += 1
        else:
            print(f"  No issues found in {spec_file.name}")
    
    print(f"\nFixed {fixed_count} out of {len(spec_files)} spec files")

if __name__ == "__main__":
    main() 