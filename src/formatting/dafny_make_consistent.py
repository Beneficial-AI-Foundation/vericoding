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

def check_vc_description(content: str, file_path: Path) -> str:
    """Check vc-description for malformed comment blocks and remove empty lines at beginning/end.
    
    Raises an error if:
    - Any line starts with '/*' but is not the first line of the section
    - Any line ends with '*/' but is not the last line of the section
    
    Returns the content with empty lines removed from beginning and end.
    """
    if not content:
        return ""
    
    lines = content.split('\n')
    
    # Remove empty lines at the beginning
    while lines and lines[0].strip() == '':
        lines = lines[1:]
    
    # Remove empty lines at the end
    while lines and lines[-1].strip() == '':
        lines = lines[:-1]

    # Check for lines starting with '/*' that are not the first line
    comment_start = False
    for i, line in enumerate(lines):
        stripped_line = line.lstrip()
        if stripped_line.startswith('/*'):
            if i > 0:
                raise ValueError(f"Line {i+1} in {file_path} starts with '/*' but is not the first line of vc-description")
            elif not line.startswith('/*'):
                raise ValueError(f"Line {i+1} in {file_path} starts with '/*' but there is an unexpected indent")
            else:
                lines[i] = line[2:].lstrip()
                comment_start = True

    # Check for lines ending with '*/' that are not the last line
    comment_end = False
    for i, line in enumerate(lines):
        stripped_line = line.rstrip()
        if stripped_line.endswith('*/'):
            if i < len(lines) - 1:
                raise ValueError(f"Line {i+1} in {file_path} ends with '*/' but is not the last line of vc-description")
            else:
                lines[i] = stripped_line[:-2].rstrip()
                comment_end = True
    
    if (not comment_start and comment_end) or (comment_start and not comment_end):
        raise ValueError(f"vc-description in {file_path} has a malformed comment block")
    
    return '\n'.join(lines)

def check_for_tag(content: str, key: str, correct_key: str, tag: str, correct_line: str) -> str:
    """
    Remove lines containing the specified tag as a substring.
    Validate that these lines have the correct format and are in the correct section before removal.
    
    Args:
        content: The input string content
        key: The current section key (e.g., "vc-preamble")
        correct_key: The expected section key for this tag (e.g., "vc-spec")
        tag: The tag to look for (e.g., "<vc-spec>" or "</vc-spec>")
        correct_line: The expected line format when stripped (e.g., "-- <vc-spec>")
        
    Returns:
        The content with valid tag lines removed
        
    Raises:
        ValueError: If the tag is found in the wrong section or doesn't match the expected format
    """
    lines = content.splitlines()
    result_lines = []
    
    for line in lines:
        stripped = line.strip()
        
        # Check for the tag
        if tag in line:
            # Check if we're in the correct section
            if key != correct_key:
                raise ValueError(f"Tag '{tag}' found in section '{key}' but expected in section '{correct_key}'")
            
            # Check if the line format is correct
            if stripped != correct_line:
                raise ValueError(f"Invalid {tag} line format. Expected '{correct_line}', got: '{line}'")
            
            # Skip this line (don't add to result)
            continue
            
        # Keep all other lines
        result_lines.append(line)
    
    return '\n'.join(result_lines)

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
        # validate_spec_keys(spec, required_keys, file_path)
        
        # Check vc-description for malformed comment blocks and clean up empty lines
        if 'vc-description' in spec and isinstance(spec['vc-description'], str):
            spec['vc-description'] = check_vc_description(spec['vc-description'], file_path)
        else:
            raise ValueError(f"vc-description not found in {file_path}")
        
        for key, value in spec.items():
            if isinstance(value, str):
                value = check_for_tag(value, key, 'vc-spec', '<vc-spec>', '// <vc-spec>')
                value = check_for_tag(value, key, 'vc-spec', '</vc-spec>', '// </vc-spec>')
                value = check_for_tag(value, key, 'vc-helpers', '<vc-helpers>', '// <vc-helpers>')
                value = check_for_tag(value, key, 'vc-helpers', '</vc-helpers>', '// </vc-helpers>')
                value = check_for_tag(value, key, 'vc-code', '<vc-code>', '// <vc-code>')
                value = check_for_tag(value, key, 'vc-code', '</vc-code>', '// </vc-code>')
                spec[key] = value
        # Normalize all sections
        for key, value in spec.items():
            if isinstance(value, str):
                spec[key] = normalize_section_content(value)
        
        # Write back to the file using spec_to_yaml to preserve structure
        spec_to_yaml(spec, file_path, required_keys)
        
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
    for folder in dafny_dir.iterdir():
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
