#!/usr/bin/env python3
"""
Script to generate YAML files from Lean files in the unformatted directory.
For each XXX.lean file, creates a corresponding XXX.yaml file with the specified format.
"""

import os
import glob
from pathlib import Path

def generate_yaml_from_lean(lean_file_path):
    """Generate a YAML file from a Lean file following the specified format."""
    
    # Read the Lean file content
    with open(lean_file_path, 'r', encoding='utf-8') as f:
        lean_content = f.read()
    
    # Create the YAML content
    yaml_content = "vc-description: |-\n\nvc-preamble: |-\n"
    
    # Add the Lean content with two spaces at the start of each line
    lean_lines = lean_content.split('\n')
    indented_lean_lines = ["  " + line for line in lean_lines]
    yaml_content += '\n'.join(indented_lean_lines)
    
    # Add the ending sections
    yaml_content += "\n\nvc-helpers: |-\n\nvc-definitions: |-\n\nvc-theorems: |-\n\nvc-postamble: |-\n"
    
    # Write the YAML file
    yaml_file_path = lean_file_path.replace('.lean', '.yaml')
    with open(yaml_file_path, 'w', encoding='utf-8') as f:
        f.write(yaml_content)
    
    print(f"Generated: {yaml_file_path}")

def main():
    """Main function to process all Lean files in the unformatted directory."""
    
    # Define the unformatted directory path
    unformatted_dir = "/home/shaowei/projects/vericoding/benchmarks/lean/numpy_triple/poor/unformatted"
    
    # Find all .lean files in the directory
    lean_files = glob.glob(os.path.join(unformatted_dir, "*.lean"))
    
    if not lean_files:
        print(f"No .lean files found in {unformatted_dir}")
        return
    
    print(f"Found {len(lean_files)} .lean files to process")
    
    # Process each Lean file
    for lean_file in lean_files:
        try:
            generate_yaml_from_lean(lean_file)
        except Exception as e:
            print(f"Error processing {lean_file}: {e}")
    
    print(f"Completed processing {len(lean_files)} files")

if __name__ == "__main__":
    main()
