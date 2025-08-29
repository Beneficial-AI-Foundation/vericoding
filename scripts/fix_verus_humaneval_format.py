#!/usr/bin/env python3

import yaml
from pathlib import Path
import re

# Directory paths
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/verus/humaneval/yaml")
SPEC_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/verus/humaneval/spec")

def clean_description(description: str) -> str:
    """Remove Lean-style comments /-- and -/ from description."""
    if not description:
        return ""
    
    # Remove /-- at the beginning and -/ at the end
    lines = description.split('\n')
    cleaned_lines = []
    
    for line in lines:
        line = line.strip()
        # Skip /-- and -/ lines
        if line == '/--' or line == '-/':
            continue
        # Remove /-- from beginning of line
        if line.startswith('/--'):
            line = line[3:].strip()
        # Remove -/ from end of line
        if line.endswith('-/'):
            line = line[:-2].strip()
        
        if line:  # Only add non-empty lines
            cleaned_lines.append(line)
    
    return '\n'.join(cleaned_lines)

def reorder_yaml_sections(yaml_data: dict) -> dict:
    """Reorder YAML sections to match expected format."""
    ordered_data = {}
    
    # Expected order: preamble, helpers, description, spec, code, postamble
    section_order = ['vc-preamble', 'vc-helpers', 'vc-description', 'vc-spec', 'vc-code', 'vc-postamble']
    
    for section in section_order:
        if section in yaml_data:
            if section == 'vc-helpers':
                # Ensure helpers is empty
                ordered_data[section] = ""
            elif section == 'vc-description':
                # Clean the description
                description = str(yaml_data[section]) if yaml_data[section] else ""
                ordered_data[section] = clean_description(description)
            else:
                ordered_data[section] = yaml_data[section]
    
    return ordered_data

def save_yaml_with_format(data: dict, file_path: Path) -> None:
    """Save YAML file with proper literal block format."""
    output_lines = []
    
    for section_name, section_content in data.items():
        output_lines.append(f"{section_name}: |-")
        
        if section_content and str(section_content).strip():
            content_lines = str(section_content).split('\n')
            for line in content_lines:
                # Preserve original indentation but ensure at least 2 spaces
                if line.strip():
                    output_lines.append(f"  {line}")
                else:
                    output_lines.append("")
        else:
            # Empty section
            output_lines.append("")
        
        output_lines.append("")
    
    # Write to file
    with open(file_path, 'w') as f:
        f.write('\n'.join(output_lines).rstrip() + '\n')

def verus_yaml_to_code(data: dict) -> str:
    """Convert YAML dict to Verus spec file."""
    output = []
    
    # Preamble
    if data.get('vc-preamble'):
        output.append(str(data['vc-preamble']).strip())
        output.append("")
    
    # Helpers (should be empty, but include if present)
    if data.get('vc-helpers') and str(data['vc-helpers']).strip():
        output.append(str(data['vc-helpers']).strip())
        output.append("")
    
    # Description as comment
    if data.get('vc-description') and str(data['vc-description']).strip():
        output.append("/*")
        output.append(str(data['vc-description']).strip())
        output.append("*/")
        output.append("")
    
    # Spec
    if data.get('vc-spec'):
        output.append(str(data['vc-spec']).strip())
    
    # Code
    if data.get('vc-code'):
        output.append(str(data['vc-code']).strip())
        output.append("")
    
    # Postamble
    if data.get('vc-postamble'):
        output.append(str(data['vc-postamble']).strip())
    
    return '\n'.join(output)

def process_yaml_file(yaml_path: Path) -> bool:
    """Process a single YAML file."""
    try:
        print(f"Processing {yaml_path.name}...")
        
        # Load YAML
        with open(yaml_path, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        if not yaml_data:
            print(f"  Warning: Empty YAML file")
            return False
        
        # Reorder and clean sections
        ordered_data = reorder_yaml_sections(yaml_data)
        
        # Save back to YAML with proper format
        save_yaml_with_format(ordered_data, yaml_path)
        
        print(f"  ✓ Fixed format and section order")
        return True
        
    except Exception as e:
        print(f"  ✗ Error processing {yaml_path.name}: {e}")
        return False

def create_spec_files():
    """Create Verus spec files from YAML files."""
    print(f"\nCreating spec files in {SPEC_DIR}...")
    
    # Create spec directory
    SPEC_DIR.mkdir(exist_ok=True)
    
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to convert")
    
    converted = 0
    for yaml_file in yaml_files:
        try:
            # Load YAML
            with open(yaml_file, 'r') as f:
                yaml_data = yaml.safe_load(f)
            
            if not yaml_data:
                continue
            
            # Convert to Verus code
            verus_code = verus_yaml_to_code(yaml_data)
            
            # Create spec file
            spec_file = SPEC_DIR / f"{yaml_file.stem}.rs"
            with open(spec_file, 'w') as f:
                f.write(verus_code)
            
            converted += 1
            print(f"  ✓ {yaml_file.name} -> {spec_file.name}")
            
        except Exception as e:
            print(f"  ✗ Failed to convert {yaml_file.name}: {e}")
    
    print(f"Successfully converted {converted} files to specs")

def main():
    """Main function to process all Verus HumanEval YAML files."""
    print("=== Fixing Verus HumanEval YAML Format ===")
    
    if not YAML_DIR.exists():
        print(f"Error: YAML directory not found: {YAML_DIR}")
        return
    
    # Get all YAML files
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to process")
    
    if not yaml_files:
        print("No YAML files found!")
        return
    
    # Process each YAML file
    processed = 0
    for yaml_file in yaml_files:
        if process_yaml_file(yaml_file):
            processed += 1
    
    print(f"\n✓ Successfully processed {processed}/{len(yaml_files)} YAML files")
    
    # Create spec files
    create_spec_files()
    
    print("\n=== Processing Complete ===")
    print("Next steps:")
    print(f"1. Check the reformatted YAML files in: {YAML_DIR}")
    print(f"2. Review the generated spec files in: {SPEC_DIR}")
    print("3. Run Verus verification on the spec files")

if __name__ == "__main__":
    main()
