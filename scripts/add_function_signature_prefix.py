#!/usr/bin/env python3

import re
from pathlib import Path
import yaml

# Directory
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")

def update_description_with_signature_prefix(description: str) -> str:
    """Add 'function_signature:' prefix to function signatures in description."""
    if not description or not description.strip():
        return description
    
    lines = description.split('\n')
    updated_lines = []
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # Check if this line looks like a function signature (starts with def, method, function, etc.)
        if (stripped.startswith('def ') or 
            stripped.startswith('method ') or 
            stripped.startswith('function ') or
            re.match(r'^[a-zA-Z_]\w*\s*\(.*\)\s*(?:->|returns|:)', stripped)):
            
            # Add function_signature: prefix if not already present
            if not line.lstrip().startswith('function_signature:'):
                indent = len(line) - len(line.lstrip())
                updated_lines.append(' ' * indent + 'function_signature: ' + stripped)
            else:
                updated_lines.append(line)
        else:
            updated_lines.append(line)
    
    return '\n'.join(updated_lines)

def update_yaml_file(yaml_path: Path) -> bool:
    """Update description in a single YAML file."""
    try:
        with open(yaml_path, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        # Get current description
        current_description = yaml_data.get('vc-description', '')
        if not current_description:
            return False
            
        # Update the description
        updated_description = update_description_with_signature_prefix(str(current_description))
        
        # Only update if there was a change
        if updated_description != str(current_description):
            yaml_data['vc-description'] = updated_description
            
            # Write back in proper order with literal format
            ordered_data = {}
            for section in ['vc-preamble', 'vc-helpers', 'vc-description', 'vc-spec', 'vc-code', 'vc-postamble']:
                if section in yaml_data:
                    ordered_data[section] = yaml_data[section]
            
            output_lines = []
            for section_name, section_content in ordered_data.items():
                output_lines.append(f"{section_name}: |-")
                if section_content and str(section_content).strip():
                    content_lines = str(section_content).split('\n')
                    for line in content_lines:
                        if line.strip() or not content_lines[-1].strip():
                            output_lines.append(f"  {line}")
                else:
                    output_lines.append("")
                output_lines.append("")
            
            with open(yaml_path, 'w') as f:
                f.write('\n'.join(output_lines).rstrip() + '\n')
            
            print(f"Added function_signature prefix in {yaml_path.name}")
            return True
        
        return False
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Add function_signature prefix to all YAML files."""
    if not YAML_DIR.exists():
        print(f"YAML directory not found: {YAML_DIR}")
        return
    
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to process")
    
    updated = 0
    for yaml_file in yaml_files:
        if update_yaml_file(yaml_file):
            updated += 1
    
    print(f"Successfully added function_signature prefix in {updated} files")

if __name__ == "__main__":
    main()
