#!/usr/bin/env python3
"""Clean up YAML files by removing comment tags that are now added automatically by the adapter."""

import yaml
import re
from pathlib import Path

def clean_yaml_file(yaml_path: Path):
    """Restore original YAML format with comment tags."""
    print(f"Restoring: {yaml_path}")
    
    # Read the YAML file
    with open(yaml_path, 'r') as f:
        data = yaml.safe_load(f)
    
    # Restore comment tags for each section
    sections_to_restore = ['vc-helpers', 'vc-spec', 'vc-code']
    
    for section in sections_to_restore:
        if section in data and data[section]:
            content = data[section]
            # Add opening and closing tags
            if section == 'vc-helpers':
                data[section] = f"// <vc-helpers>\n{content}\n// </vc-helpers>"
            elif section == 'vc-spec':
                data[section] = f"// <vc-spec>\n{content}\n// </vc-spec>"
            elif section == 'vc-code':
                data[section] = f"// <vc-code>\n{content}\n// </vc-code>"
    
    # Write back the restored YAML with readable format
    with open(yaml_path, 'w') as f:
        yaml.dump(data, f, default_flow_style=False, sort_keys=False, 
                 allow_unicode=True, width=float("inf"), default_style='|')
    
    print(f"  ✓ Restored {yaml_path}")

def main():
    """Restore all YAML files in the benchmarks directory to original format."""
    yaml_dir = Path("benchmarks/vericoding_dafny/dafnybench/yaml")
    
    if not yaml_dir.exists():
        print(f"Directory not found: {yaml_dir}")
        return
    
    yaml_files = list(yaml_dir.glob("*.yaml")) + list(yaml_dir.glob("*.yml"))
    
    if not yaml_files:
        print("No YAML files found")
        return
    
    print(f"Found {len(yaml_files)} YAML files to restore")
    print()
    
    for yaml_file in yaml_files:
        try:
            clean_yaml_file(yaml_file)
        except Exception as e:
            print(f"  ✗ Error restoring {yaml_file}: {e}")
    
    print()
    print("YAML restoration complete!")

if __name__ == "__main__":
    main()
