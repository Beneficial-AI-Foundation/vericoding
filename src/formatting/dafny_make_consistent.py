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

def validate_spec_keys(spec: Dict[str, Any], required_keys: list, file_path: Path) -> None:
    """Validate that spec has exactly the same keys as required keys."""
    if spec is None:
        print(f"Warning: {file_path} is empty or invalid YAML")
        return

    spec_keys = set(spec.keys())
    required_keys_set = set(required_keys)
    
    if spec_keys != required_keys_set:
        missing_keys = required_keys_set - spec_keys
        extra_keys = spec_keys - required_keys_set
        
        error_msg = f"Key mismatch in {file_path}:"
        if missing_keys:
            error_msg += f" Missing keys: {sorted(missing_keys)}"
        if extra_keys:
            error_msg += f" Extra keys: {sorted(extra_keys)}"
        
        raise ValueError(error_msg)

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

    required_keys = ['vc-description', 'vc-preamble', 'vc-helpers', 
                     'vc-spec', 'vc-code', 'vc-postamble']
                     
    try:
        # Import ruamel.yaml here to avoid circular imports
        from ruamel.yaml import YAML
        
        # Read the YAML file with ruamel.yaml to preserve structure
        yaml_loader = YAML()
        yaml_loader.preserve_quotes = True
        
        with open(file_path, 'r', encoding='utf-8') as f:
            spec = yaml_loader.load(f)

        # Check that spec has exactly the same keys as required keys
        validate_spec_keys(spec, required_keys, file_path)
            
        # Normalize all sections
        for key, value in spec.items():
            if isinstance(value, str):
                spec[key] = normalize_section_content(value)
        
        # Write back to the file using spec_to_yaml to preserve structure
        # spec_to_yaml(spec, file_path, required_keys)
        
        # print(f"Processed: {file_path}")
        
    except Exception as e:
        print(f"Error processing {file_path}: {e}")

def main():
    """Main function to process all YAML files in directories with yaml subfolders."""
    # Get the lean benchmarks directory
    dafny_dir = Path('benchmarks/dafny')
    
    if not dafny_dir.exists():
        print(f"Error: Directory {dafny_dir} not found")
        return
    
    total_files_processed = 0
    
    # Loop through all immediate folders in the dafny directory
    for folder in [ dafny_dir / 'dafnybench' ]:
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
                    try:
                        process_yaml_file(yaml_file)
                        total_files_processed += 1
                    except ValueError as e:
                        print(f"  Validation error in {yaml_file.name}: {e}")
                        # Continue processing other files instead of stopping
                    except Exception as e:
                        print(f"  Error processing {yaml_file.name}: {e}")
                        # Continue processing other files instead of stopping
                
                print(f"  Completed processing {folder.name}/yaml/")
    
    print(f"Processing complete! Total files processed: {total_files_processed}")

if __name__ == "__main__":
    main()
