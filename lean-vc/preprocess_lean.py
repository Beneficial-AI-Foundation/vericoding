#!/usr/bin/env python3
import re
import os
from pathlib import Path

def preprocess_lean_code(content):
    """Pre-process Lean code to fix common syntax issues."""
    
    # Fix deprecated get! usage
    content = re.sub(r'(\w+)\.get!\s*\(([^)]+)\)', r'\1[\2]!', content)
    
    # Fix deprecated get usage
    content = re.sub(r'(\w+)\.get\s*\(([^)]+)\)', r'\1[\2]?', content)
    
    # Fix common syntax errors
    content = re.sub(r':= :=', ':=', content)  # Fix double :=
    content = re.sub(r'def (\w+)\s*\ndef \1', r'def \1', content)  # Fix duplicate def
    
    # Add common imports if not present
    common_imports = [
        'import Mathlib.Data.Nat.Prime',
        'import Mathlib.Data.List.Basic', 
        'import Mathlib.Data.String.Basic',
        'import Mathlib.Data.Int.Basic',
        'import Mathlib.Data.Rat.Basic',
        'import Mathlib.Tactic.Basic',
        'import Mathlib.Tactic.Ring',
        'import Mathlib.Tactic.Linarith'
    ]
    
    # Check if any imports are missing and add them
    existing_imports = re.findall(r'import\s+([^\s]+)', content)
    for imp in common_imports:
        if imp not in content:
            # Add import at the beginning of the file
            content = imp + '\n' + content
    
    return content

def process_file(file_path):
    """Process a single Lean file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    processed_content = preprocess_lean_code(content)
    
    if processed_content != content:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(processed_content)
        return True
    
    return False

def main():
    """Process all Lean files in the current directory."""
    current_dir = Path('.')
    lean_files = list(current_dir.glob('*.lean'))
    
    print(f"Processing {len(lean_files)} Lean files...")
    
    fixed_count = 0
    for lean_file in lean_files:
        if process_file(lean_file):
            print(f"Fixed {lean_file.name}")
            fixed_count += 1
    
    print(f"Fixed {fixed_count} out of {len(lean_files)} files")

if __name__ == "__main__":
    main() 