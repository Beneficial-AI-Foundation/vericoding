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

def generate_method_description(method_name: str, task_num: int, yaml_data: dict) -> str:
    """Generate an informative description for a method."""
    
    # First try to get from Lean
    lean_desc = extract_description_from_lean(task_num)
    if lean_desc and lean_desc != "":
        return lean_desc
    
    # Fallback: analyze the spec to create a description
    spec_content = yaml_data.get('vc-spec', '')
    
    # Extract method signature
    method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
    if not method_match:
        return f"Method {method_name} from HumanEval task {task_num:03d}."
    
    signature = method_match.group(0)
    
    # Extract ensures clauses for informal description
    ensures_matches = re.findall(r'ensures\s+([^/\n]+)', spec_content)
    
    description_parts = [f"```dafny\n{signature}\n```"]
    
    if ensures_matches:
        description_parts.append("\nThis method should:")
        for i, ensure in enumerate(ensures_matches[:3], 1):  # Limit to 3 main ensures
            ensure_clean = ensure.strip().rstrip(',')
            # Convert formal condition to informal description
            informal = convert_formal_to_informal(ensure_clean)
            description_parts.append(f"{i}. {informal}")
    
    return "\n".join(description_parts)

def convert_formal_to_informal(formal_condition: str) -> str:
    """Convert a formal ensures clause to informal description."""
    
    # Common patterns and their informal equivalents
    patterns = [
        (r'\|(\w+)\|\s*==\s*\|(\w+)\|', r'have the same length as \2'),
        (r'\|result\|\s*==\s*\|(\w+)\|', r'return a sequence with the same length as \1'),
        (r'\|result\|\s*<=\s*(\d+)\s*\*\s*\|(\w+)\|', r'return a result at most \1 times the length of \2'),
        (r'forall\s+\w+\s*::\s*.*==>\s*(.+)', r'ensure that \1'),
        (r'result\[(\w+)\]\s*==\s*(\w+)\[(\w+)\]', r'preserve elements correctly'),
        (r'is_palindrome\(result\)', r'return a palindrome'),
        (r'starts_with\(result,\s*(\w+)\)', r'return a string that starts with \1'),
    ]
    
    informal = formal_condition
    for pattern, replacement in patterns:
        informal = re.sub(pattern, replacement, informal, flags=re.IGNORECASE)
    
    # Clean up remaining formal syntax
    informal = re.sub(r'\s+', ' ', informal)
    informal = informal.strip()
    
    return informal

def update_yaml_file(yaml_path: Path):
    """Update a single YAML file with better description."""
    try:
        with open(yaml_path, 'r') as f:
            content = f.read()
        
        # Parse YAML
        yaml_data = yaml.safe_load(content)
        
        # Extract task number from filename
        filename = yaml_path.stem
        task_num = None
        try:
            # Handle various formats: 000-task, task, task__method
            parts = filename.split('-')
            if len(parts) >= 2 and parts[0].isdigit():
                task_num = int(parts[0])
            else:
                # Try to find any 3-digit number at the start
                match = re.match(r'^(\d{3})', filename)
                if match:
                    task_num = int(match.group(1))
        except:
            pass
        
        if task_num is None:
            print(f"Could not extract task number from {filename}")
            return False
        
        # Extract method name
        method_name = "main"  # default
        if '__' in filename:
            method_name = filename.split('__')[1]
        else:
            # Single method file, extract from spec
            spec_content = yaml_data.get('vc-spec', '')
            method_match = re.search(r'method\s+(\w+)', spec_content)
            if method_match:
                method_name = method_match.group(1)
        
        # Generate new description
        new_description = generate_method_description(method_name, task_num, yaml_data)
        
        # Update the YAML data
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
        
        # Write back with proper formatting
        with open(yaml_path, 'w') as f:
            yaml.dump(ordered_data, f, default_flow_style=False, allow_unicode=True, 
                     default_style='|-' if len(str(ordered_data)) > 100 else None)
        
        print(f"Updated {yaml_path.name}")
        return True
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Update all YAML files with better descriptions and correct order."""
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
