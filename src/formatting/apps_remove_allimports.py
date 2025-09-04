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
        
        # Process vc-preamble specifically to remove 'import Imports.AllImports'
        if 'vc-preamble' in spec:
            preamble = spec['vc-preamble']
            lines = preamble.split('\n')
            filtered_lines = [line for line in lines if line.strip() != 'import Imports.AllImports']
            spec['vc-preamble'] = normalize_section_content('\n'.join(filtered_lines))
        
        # Normalize all other sections
        for key, value in spec.items():
            if key != 'vc-preamble' and isinstance(value, str):
                spec[key] = normalize_section_content(value)
        
        # Get the required keys in the order they appeared in the original file
        required_keys = list(spec.keys())
        
        # Write back to the file using spec_to_yaml to preserve structure
        spec_to_yaml(spec, file_path, required_keys)
        
        # print(f"Processed: {file_path}")
        
    except Exception as e:
        print(f"Error processing {file_path}: {e}")

def main():
    """Main function to process all YAML files in apps_train directory."""
    # Get the directory containing this script
    apps_train_dir = Path('benchmarks/lean/apps_train')
    
    if not apps_train_dir.exists():
        print(f"Error: Directory {apps_train_dir} not found")
        return
    
    # Find all YAML files
    yaml_files = list(apps_train_dir.glob('*.yaml'))
    
    if not yaml_files:
        print(f"No YAML files found in {apps_train_dir}")
        return
    
    print(f"Found {len(yaml_files)} YAML files to process")
    
    # Process each file
    count = 0
    for yaml_file in yaml_files:
        count += 1
        if count % 100 == 0:
            print(f"Processing {count} of {len(yaml_files)}")
        process_yaml_file(yaml_file)
    
    print("Processing complete!")

if __name__ == "__main__":
    main()
