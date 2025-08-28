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

def reorder_yaml_sections(yaml_content: str) -> tuple[str, bool]:
    """Reorder YAML sections to: preamble, helpers, description, spec, code, postamble."""
    
    # Parse sections using regex (safer than YAML parsing for malformed files)
    sections = {}
    
    # Extract each section
    section_patterns = [
        ('vc-preamble', r'vc-preamble:\s*\|-?\s*(.*?)(?=\n\w+:|$)'),
        ('vc-helpers', r'vc-helpers:\s*\|-?\s*(.*?)(?=\n\w+:|$)'),
        ('vc-description', r'vc-description:\s*\|-?\s*(.*?)(?=\n\w+:|$)'),
        ('vc-spec', r'vc-spec:\s*\|-?\s*(.*?)(?=\n\w+:|$)'),
        ('vc-code', r'vc-code:\s*\|-?\s*(.*?)(?=\n\w+:|$)'),
        ('vc-postamble', r'vc-postamble:\s*\|-?\s*(.*?)(?=\n\w+:|$)')
    ]
    
    for section_name, pattern in section_patterns:
        match = re.search(pattern, yaml_content, re.DOTALL | re.MULTILINE)
        if match:
            content = match.group(1).strip()
            sections[section_name] = content
    
    # Check if we found the main sections
    if 'vc-spec' not in sections:
        return yaml_content, False
    
    # Build the reordered content
    output_lines = []
    
    # Order: preamble, helpers, description, spec, code, postamble
    ordered_sections = ['vc-preamble', 'vc-helpers', 'vc-description', 'vc-spec', 'vc-code', 'vc-postamble']
    
    for section_name in ordered_sections:
        if section_name in sections:
            content = sections[section_name]
            output_lines.append(f"{section_name}: |-")
            if content:
                # Indent content properly
                for line in content.split('\n'):
                    if line.strip():
                        output_lines.append(f"  {line}")
                    else:
                        output_lines.append("")
            else:
                output_lines.append("")
            output_lines.append("")
    
    return '\n'.join(output_lines).rstrip() + '\n', True

def update_yaml_file(yaml_path: Path) -> bool:
    """Update a YAML file with better description and correct order."""
    try:
        with open(yaml_path, 'r') as f:
            content = f.read()
        
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
            spec_match = re.search(r'method\s+(\w+)', content)
            if spec_match:
                method_name = spec_match.group(1)
        
        # Get current description
        desc_match = re.search(r'vc-description:\s*\|-?\s*(.*?)(?=\n\w+:|$)', content, re.DOTALL)
        current_description = desc_match.group(1).strip() if desc_match else ""
        
        # Only improve description if it's generic/poor
        if ("HumanEval task:" in current_description and "Implement according to the specification" in current_description) or \
           ("Auxiliary method" in current_description) or \
           not current_description:
            
            # Get spec content for better description
            spec_match = re.search(r'vc-spec:\s*\|-?\s*(.*?)(?=\n\w+:|$)', content, re.DOTALL)
            spec_content = spec_match.group(1) if spec_match else ""
            
            new_description = create_method_description(method_name, task_num, spec_content)
            
            # Replace the description in content
            if desc_match:
                content = content.replace(desc_match.group(0), f"vc-description: |-\n  {new_description}")
            else:
                # Add description if missing
                content = f"vc-description: |-\n  {new_description}\n\n" + content
        
        # Reorder sections
        reordered_content, success = reorder_yaml_sections(content)
        if not success:
            print(f"Could not reorder sections in {filename}")
            return False
        
        # Write back
        with open(yaml_path, 'w') as f:
            f.write(reordered_content)
        
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
