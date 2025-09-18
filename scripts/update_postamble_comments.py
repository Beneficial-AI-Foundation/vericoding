#!/usr/bin/env python3
"""
Script to update /- to /-- in vc-postamble sections of YAML files.
"""

import os
import re
from pathlib import Path

def update_yaml_file(file_path):
    """Update /- to /-- in vc-postamble section of a YAML file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check if file has vc-postamble section
        if 'vc-postamble:' not in content:
            return False, "No vc-postamble section found"
        
        # Split content into lines
        lines = content.split('\n')
        updated_lines = []
        in_postamble = False
        changes_made = False
        
        for line in lines:
            if line.strip().startswith('vc-postamble:'):
                in_postamble = True
                updated_lines.append(line)
            elif in_postamble and line.strip() and not line.startswith(' ') and not line.startswith('\t'):
                # We've reached the next section (non-indented line that's not empty)
                in_postamble = False
                updated_lines.append(line)
            elif in_postamble:
                # We're in the postamble section, replace /- with /--
                if '/-' in line:
                    updated_line = line.replace('/-', '/--')
                    updated_lines.append(updated_line)
                    changes_made = True
                else:
                    updated_lines.append(line)
            else:
                updated_lines.append(line)
        
        if changes_made:
            # Write the updated content back
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write('\n'.join(updated_lines))
            return True, f"Updated {file_path}"
        else:
            return False, f"No changes needed in {file_path}"
            
    except Exception as e:
        return False, f"Error processing {file_path}: {str(e)}"

def main():
    """Process all YAML files in the fvapps_good directory."""
    base_dir = Path("/home/qd/Projects/safeguarded/baif/vericoding/benchmarks/lean/fvapps_good/yaml")
    
    if not base_dir.exists():
        print(f"Directory {base_dir} does not exist!")
        return
    
    yaml_files = list(base_dir.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to process")
    
    updated_count = 0
    error_count = 0
    
    for i, yaml_file in enumerate(yaml_files, 1):
        if i % 100 == 0:
            print(f"Processing file {i}/{len(yaml_files)}: {yaml_file.name}")
        
        success, message = update_yaml_file(yaml_file)
        if success:
            updated_count += 1
            if i <= 10:  # Show details for first 10 files
                print(f"✓ {message}")
        else:
            if "No changes needed" not in message:
                error_count += 1
                print(f"✗ {message}")
    
    print(f"\nProcessing complete!")
    print(f"Files updated: {updated_count}")
    print(f"Files with errors: {error_count}")
    print(f"Total files processed: {len(yaml_files)}")

if __name__ == "__main__":
    main()
