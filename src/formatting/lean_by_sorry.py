#!/usr/bin/env python3
"""
Script to remove 'import Imports.AllImports' lines from vc-preamble sections
in all YAML files in the apps_train directory.
"""

import os
from pathlib import Path
from typing import Any, Dict
import sys

# Add src directory to path to import convert_from_yaml
sys.path.append(str(Path(__file__).parent.parent))
from convert_from_yaml import spec_to_yaml

def normalize_section_content(content: str) -> str:
    """Normalize section content by removing leading empty lines and reducing consecutive empty lines to one."""
    if not content:
        return ""
    
    lines = content.split('\n')
    
    # Remove empty lines at the start
    while lines and lines[0].strip() == '':
        lines = lines[1:]
    
    # Reduce consecutive empty lines to single empty lines
    normalized_lines = []
    prev_empty = False
    
    for line in lines:
        if line.strip() == '':
            if not prev_empty:
                normalized_lines.append('')
                prev_empty = True
        else:
            normalized_lines.append(line)
            prev_empty = False
    
    # Join and apply rstrip
    return '\n'.join(normalized_lines).rstrip()

def process_yaml_file(file_path: Path) -> None:
    """Process a single YAML file to remove 'import Imports.AllImports' lines and normalize sections."""
    try:
        # Import ruamel.yaml here to avoid circular imports
        from ruamel.yaml import YAML
        
        # Read the YAML file with ruamel.yaml to preserve structure
        yaml_loader = YAML()
        yaml_loader.preserve_quotes = True
        
        with open(file_path, 'r', encoding='utf-8') as f:
            spec = yaml_loader.load(f)
        
        if spec is None:
            print(f"Warning: {file_path} is empty or invalid YAML")
            return
            
        # Process vc-theorems section if it exists
        if 'vc-theorems' in spec:
            theorems_content = spec['vc-theorems']
            
            # Check if vc-theorems has exactly one 'sorry'
            sorry_count = theorems_content.count('sorry')
            if sorry_count != 1:
                print(f"Error in {file_path}: vc-theorems section has {sorry_count} 'sorry' statements, expected exactly 1")
                return
            
            # Check line-by-line for exactly one line that is only 'sorry' when stripped
            lines = theorems_content.split('\n')
            sorry_line_indices = []
            for i, line in enumerate(lines):
                if line.strip() == 'sorry':
                    sorry_line_indices.append(i)
            
            if len(sorry_line_indices) != 1:
                print(f"Error in {file_path}: Found {len(sorry_line_indices)} lines with only 'sorry', expected exactly 1")
                return
            
            sorry_line_idx = sorry_line_indices[0]
            
            # Check that the line before ends with ":="
            if sorry_line_idx == 0:
                print(f"Error in {file_path}: 'sorry' line is the first line, no previous line to check")
                return
            
            prev_line = lines[sorry_line_idx - 1]

            # Already has "by" at the end
            if prev_line.strip().endswith('by'):
                print(f"Error in {file_path}: Line before 'sorry' already ends with 'by'. Found: '{prev_line.strip()}'")
                return
            
            # Does not have "by" at the end but has ":="
            if not prev_line.strip().endswith(':='):
                print(f"Error in {file_path}: Line before 'sorry' does not end with ':='. Found: '{prev_line.strip()}'")
                return
            
            # Append " by" to the end of the line before 'sorry'
            lines[sorry_line_idx - 1] = prev_line.rstrip() + ' by'
            
            # Update the vc-theorems content
            spec['vc-theorems'] = normalize_section_content('\n'.join(lines))   
            print(f"Fixed: {file_path}")
        
        # Normalize all other sections
        for key, value in spec.items():
            if key not in ['vc-proof', 'vc-condition', 'vc-implementation', 'vc-signature'] and isinstance(value, str):
                spec[key] = normalize_section_content(value)
        
        # Get the required keys in the order they appeared in the original file
        required_keys = ['vc-description', 'vc-preamble', 'vc-helpers', 
                         'vc-definitions', 'vc-theorems', 'vc-postamble']
        
        # Write back to the file using spec_to_yaml to preserve structure
        spec_to_yaml(spec, file_path, required_keys)
        
        # print(f"Processed: {file_path}")
        
    except Exception as e:
        print(f"Error processing {file_path}: {e}")

def main():
    """Main function to process all YAML files in directories with yaml subfolders."""
    # Get the lean benchmarks directory
    lean_dir = Path('benchmarks/lean')
    
    if not lean_dir.exists():
        print(f"Error: Directory {lean_dir} not found")
        return
    
    total_files_processed = 0
    
    # Loop through all immediate folders in the lean directory
    # for folder in lean_dir.iterdir():
    for folder in [lean_dir / 'humaneval']:
        if folder.is_dir():
            yaml_subfolder = folder / 'yaml'
            
            # Check if this folder has a yaml subfolder
            if yaml_subfolder.exists() and yaml_subfolder.is_dir():
                print(f"Processing YAML files in {folder.name}/yaml/")
                
                # Find all YAML files in the yaml subfolder
                yaml_files = list(yaml_subfolder.glob('*.yaml'))
                
                if not yaml_files:
                    print(f"  No YAML files found in {yaml_subfolder}")
                    continue
                
                print(f"  Found {len(yaml_files)} YAML files to process")
                
                # Process each file
                count = 0
                for yaml_file in yaml_files:
                    count += 1
                    if count % 100 == 0:
                        print(f"  Processing {count} of {len(yaml_files)}")
                    process_yaml_file(yaml_file)
                    total_files_processed += 1
                
                print(f"  Completed processing {folder.name}/yaml/")
    
    print(f"Processing complete! Total files processed: {total_files_processed}")

if __name__ == "__main__":
    main()
