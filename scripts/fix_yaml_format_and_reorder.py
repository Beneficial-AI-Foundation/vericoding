#!/usr/bin/env python3

import re
from pathlib import Path
import yaml

# Directories
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")
LEAN_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/vericoding_lean/humaneval")

def extract_description_from_lean(task_num: int) -> str:
    """Extract description from corresponding Lean file."""
    lean_file = LEAN_DIR / f"HumanEval_{task_num}.yaml"
    
    if not lean_file.exists():
        return None
        
    try:
        with open(lean_file, 'r') as f:
            lean_data = yaml.safe_load(f)
            
        if 'vc-description' in lean_data:
            desc = lean_data['vc-description'].strip()
            # Clean up any Lean-specific formatting
            desc = re.sub(r'/--.*?-/', '', desc, flags=re.DOTALL)
            desc = re.sub(r'\n\s*\n\s*\n', '\n\n', desc)  # Remove excessive newlines
            return desc.strip()
    except Exception as e:
        print(f"Error reading Lean file {lean_file}: {e}")
    
    return None

def create_method_description(method_name: str, task_num: int, spec_content: str) -> str:
    """Create an informative description for a method."""
    
    # First try to get from Lean
    lean_desc = extract_description_from_lean(task_num)
    if lean_desc and lean_desc.strip():
        return lean_desc
    
    # Fallback: create a concise description based on method signature
    method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
    if method_match:
        signature = method_match.group(0).strip()
        return f"```dafny\n{signature}\n```\n\nHumanEval task {task_num:03d}: Implement the {method_name} method according to the specification."
    
    return f"HumanEval task {task_num:03d}: Implement the {method_name} method."

def update_yaml_file(yaml_path: Path) -> bool:
    """Update a YAML file with better description and correct order using literal format."""
    try:
        with open(yaml_path, 'r') as f:
            content = f.read()
        
        # Parse YAML regardless of format
        yaml_data = yaml.safe_load(content)
        
        # Extract task number from filename
        filename = yaml_path.stem
        task_num = None
        
        # Try different patterns
        patterns = [
            r'^(\d{3})-',  # 000-task
            r'^(\d{3})_',  # 000_task
            r'^(\d{1,3})-', # flexible digits
        ]
        
        for pattern in patterns:
            match = re.match(pattern, filename)
            if match:
                task_num = int(match.group(1))
                break
        
        if task_num is None:
            print(f"Could not extract task number from {filename}")
            return False
        
        # Extract method name
        method_name = "main"
        if '__' in filename:
            method_name = filename.split('__')[1]
        else:
            # Try to extract from spec section
            spec_content = yaml_data.get('vc-spec', '')
            spec_match = re.search(r'method\s+(\w+)', spec_content)
            if spec_match:
                method_name = spec_match.group(1)
        
        # Get current description
        current_description = yaml_data.get('vc-description', '').strip()
        
        # Only improve description if it's generic/poor
        if ("HumanEval task:" in current_description and "Implement according to the specification" in current_description) or \
           ("Auxiliary method" in current_description) or \
           not current_description:
            
            spec_content = yaml_data.get('vc-spec', '')
            new_description = create_method_description(method_name, task_num, spec_content)
            yaml_data['vc-description'] = new_description
        
        # Reorder sections: preamble, helpers, description, spec, code, postamble
        ordered_data = {}
        
        if 'vc-preamble' in yaml_data:
            ordered_data['vc-preamble'] = yaml_data['vc-preamble']
        
        if 'vc-helpers' in yaml_data:
            ordered_data['vc-helpers'] = yaml_data['vc-helpers']
        
        ordered_data['vc-description'] = yaml_data['vc-description']
        
        if 'vc-spec' in yaml_data:
            ordered_data['vc-spec'] = yaml_data['vc-spec']
        
        if 'vc-code' in yaml_data:
            ordered_data['vc-code'] = yaml_data['vc-code']
        
        if 'vc-postamble' in yaml_data:
            ordered_data['vc-postamble'] = yaml_data['vc-postamble']
        
        # Write back in literal format
        output_lines = []
        
        for section_name, section_content in ordered_data.items():
            output_lines.append(f"{section_name}: |-")
            if section_content and section_content.strip():
                # Split content into lines and indent
                content_lines = str(section_content).split('\n')
                for line in content_lines:
                    if line.strip() or not content_lines[-1].strip():  # Keep empty lines except trailing
                        output_lines.append(f"  {line}")
            else:
                output_lines.append("")
            output_lines.append("")
        
        # Write the file
        with open(yaml_path, 'w') as f:
            f.write('\n'.join(output_lines).rstrip() + '\n')
        
        print(f"Updated {yaml_path.name}")
        return True
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Update YAML files with better descriptions and correct order."""
    if not YAML_DIR.exists():
        print(f"YAML directory not found: {YAML_DIR}")
        return
    
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to update")
    
    updated = 0
    for yaml_file in yaml_files:
        if update_yaml_file(yaml_file):
            updated += 1
    
    print(f"Successfully updated {updated} out of {len(yaml_files)} files")

if __name__ == "__main__":
    main()
