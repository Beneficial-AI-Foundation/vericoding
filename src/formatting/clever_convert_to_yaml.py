#!/usr/bin/env python3
import os
import re
import yaml
import glob
from pathlib import Path
from convert_from_yaml import spec_to_yaml

def convert_lean_to_yaml(lean_file_path):
    """Convert a Lean file to a spec object according to the specified rules."""
    
    with open(lean_file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    lines = content.split('\n')
    
    # Find all section markers - accept any combination of dashes and spaces after initial --
    # Matches: --, ---, ---- -, -- -, --- ---, etc. followed by start_def/end_def
    start_pattern = r'--[-\s]*start_def\s+(\w+)'
    end_pattern = r'--[-\s]*end_def\s+(\w+)'
    
    sections = {}
    current_section = None
    current_content = []
    preamble_lines = []
    postamble_lines = []
    in_section = False
    nesting_level = 0
    
    for i, line in enumerate(lines):
        start_match = re.match(start_pattern, line.strip())
        end_match = re.match(end_pattern, line.strip())
        
        if start_match:
            # If we haven't started any section yet, collect preamble
            if not in_section:
                preamble_lines = lines[:i]
                in_section = True
            
            # If we're already in a section, this is a nested section
            if current_section is not None:
                nesting_level += 1
                print(f"  Warning: Found nested section '{start_match.group(1)}' inside section '{current_section}' at line {i+1}")
                # Add the nested section marker as part of the current section's content
                current_content.append(line)
                continue
            
            # This is a top-level section
            current_section = start_match.group(1)
            current_content = []
            nesting_level = 0
            
        elif end_match:
            if current_section is None:
                raise ValueError(f"Found end_def {end_match.group(1)} without matching start_def")
            
            if end_match.group(1) != current_section:
                # This is a nested section ending
                if nesting_level > 0:
                    nesting_level -= 1
                    # Add the nested section end marker as part of the current section's content
                    current_content.append(line)
                    continue
                else:
                    raise ValueError(f"Mismatched section markers: start_def {current_section} vs end_def {end_match.group(1)}")
            
            # This is the end of the current top-level section
            sections[current_section] = '\n'.join(current_content)
            current_section = None
            current_content = []
            nesting_level = 0
            
        elif current_section is not None:
            current_content.append(line)
    
    # Check for any unclosed sections
    if current_section is not None:
        raise ValueError(f"Unclosed section: {current_section}")
    
    # Collect postamble (lines after the last section)
    if in_section:
        # Find the last end_def line
        last_end_line = -1
        for i, line in enumerate(lines):
            if re.match(end_pattern, line.strip()):
                last_end_line = i
        
        if last_end_line >= 0:
            postamble_lines = lines[last_end_line + 1:]
    
    # Build spec object
    spec = {}
    
    # Add preamble if it exists and is not empty
    if preamble_lines:  
        spec['preamble'] = '\n'.join(preamble_lines).rstrip()
    
    # Add all sections
    for section_name, section_content in sections.items():
        spec[section_name] = section_content.rstrip()
    
    # Add postamble if it exists and is not empty
    if postamble_lines:
        spec['postamble'] = '\n'.join(postamble_lines).rstrip()
    
    return spec

def main():
    """Convert all Lean files in the humaneval directory to YAML."""
    
    # Get all .lean files in the humaneval directory
    lean_files = glob.glob('benchmarks/vericoding_raw/humaneval/*.lean')
    
    # Create output directory
    output_dir = Path('benchmarks/vericoding_raw/humaneval_yaml')
    output_dir.mkdir(exist_ok=True)
    
    successful_conversions = 0
    failed_conversions = 0
    
    for lean_file in lean_files:
        try:
            print(f"Converting {lean_file}...")
            
            # Convert to spec object
            spec = convert_lean_to_yaml(lean_file)
            
            # Generate output filename
            base_name = Path(lean_file).stem
            yaml_file = output_dir / f"{base_name}.yaml"
            
            # Write YAML file using spec_to_yaml
            required_keys = [     
                'vc-description',
                'vc-preamble', 
                'vc-helpers',
                'vc-signature',
                'vc-implementation',
                'vc-condition',
                'vc-proof',
                'vc-postamble'
            ]
            spec_to_yaml(spec, yaml_file, required_keys=required_keys)
            
            print(f"  -> {yaml_file}")
            successful_conversions += 1
            
        except Exception as e:
            print(f"Error converting {lean_file}: {e}")
            failed_conversions += 1
            continue
    
    print(f"\nConversion complete!")
    print(f"Successful conversions: {successful_conversions}")
    print(f"Failed conversions: {failed_conversions}")
    print(f"YAML files saved to {output_dir}")

if __name__ == "__main__":
    main()
