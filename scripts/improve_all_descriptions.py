#!/usr/bin/env python3

import re
from pathlib import Path
import yaml
import requests
from typing import Optional

# Directories
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")
LEAN_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/vericoding_lean/humaneval")

# GitHub text descriptions mapping (based on the repository structure)
GITHUB_DESCRIPTIONS = {
    0: "Check if in given list of numbers, are any two numbers closer to each other than given threshold.",
    1: "Input to this function is a string containing multiple groups of nested parentheses. Your goal is to separate those group into separate strings and return the list of those.",
    2: "Truncate a number to a given number of decimal places.",
    3: "You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. Your task is to detect if at any point the balance of account falls below zero, and at that point function should return True. Otherwise it should return False.",
    4: "For a given list of input numbers, calculate Mean Absolute Deviation around the mean of this dataset.",
    5: "Insert a number 'delimeter' between every two consecutive elements of input list `numbers'",
    # Add more as needed - this is a subset for demonstration
}

def extract_description_from_lean(task_num: int) -> Optional[str]:
    """Extract and clean description from Lean YAML file."""
    lean_file = LEAN_DIR / f"HumanEval_{task_num}.yaml"
    
    if not lean_file.exists():
        return None
        
    try:
        with open(lean_file, 'r') as f:
            lean_data = yaml.safe_load(f)
            
        if 'vc-description' not in lean_data:
            return None
            
        desc = lean_data['vc-description']
        if not desc or not desc.strip():
            return None
            
        # Remove /-- and -/ blocks and extract the content
        desc_clean = re.sub(r'/--\s*', '', desc)
        desc_clean = re.sub(r'\s*-/', '', desc_clean)
        
        # Parse the YAML-like structure inside
        try:
            # Extract function signature and docstring
            lines = desc_clean.strip().split('\n')
            result_parts = []
            
            in_docstring = False
            docstring_lines = []
            function_signature = None
            
            for line in lines:
                line = line.strip()
                if line.startswith('function_signature:'):
                    sig_match = re.search(r'"([^"]+)"', line)
                    if sig_match:
                        function_signature = sig_match.group(1)
                elif line.startswith('docstring:'):
                    in_docstring = True
                elif in_docstring:
                    if line and not line.startswith('test_cases:'):
                        # Clean up docstring line
                        clean_line = line.strip()
                        if clean_line and not clean_line.startswith('-'):
                            docstring_lines.append(clean_line)
                    else:
                        in_docstring = False
            
            if function_signature:
                result_parts.append(f"```python\n{function_signature}\n```")
            
            if docstring_lines:
                docstring = ' '.join(docstring_lines).strip()
                if docstring:
                    result_parts.append(docstring)
            
            if result_parts:
                return '\n\n'.join(result_parts)
                
        except Exception:
            # If parsing fails, just return cleaned content
            return desc_clean.strip()
            
    except Exception as e:
        print(f"Error reading Lean file {lean_file}: {e}")
    
    return None

def get_github_description(task_num: int) -> Optional[str]:
    """Get description from GitHub repository or local mapping."""
    # For now, use local mapping. Could extend to fetch from GitHub API
    return GITHUB_DESCRIPTIONS.get(task_num)

def generate_auxiliary_description(method_name: str, task_num: int, spec_content: str) -> str:
    """Generate description for auxiliary methods created during processing."""
    
    # Extract method signature
    method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
    signature = method_match.group(0) if method_match else f"method {method_name}"
    
    # Determine the type of auxiliary method
    if 'count' in method_name.lower():
        purpose = f"Count occurrences or elements related to HumanEval task {task_num:03d}."
    elif 'sort' in method_name.lower():
        purpose = f"Sort elements according to specific criteria for HumanEval task {task_num:03d}."
    elif 'reverse' in method_name.lower():
        purpose = f"Reverse elements or strings for HumanEval task {task_num:03d}."
    elif 'sum' in method_name.lower():
        purpose = f"Sum elements according to specific criteria for HumanEval task {task_num:03d}."
    elif 'get' in method_name.lower():
        purpose = f"Retrieve elements matching specific criteria for HumanEval task {task_num:03d}."
    elif 'is_' in method_name.lower():
        purpose = f"Check a condition or property for HumanEval task {task_num:03d}."
    elif 'filter' in method_name.lower():
        purpose = f"Filter elements based on criteria for HumanEval task {task_num:03d}."
    elif 'parse' in method_name.lower():
        purpose = f"Parse input according to rules for HumanEval task {task_num:03d}."
    else:
        purpose = f"Auxiliary method for HumanEval task {task_num:03d}."
    
    return f"```dafny\n{signature}\n```\n\n{purpose}"

def create_improved_description(task_num: int, method_name: str, spec_content: str, is_main_method: bool = True) -> str:
    """Create an improved description for a method."""
    
    if is_main_method:
        # For main methods, try Lean first, then GitHub, then generate
        desc = extract_description_from_lean(task_num)
        if desc:
            return desc
            
        desc = get_github_description(task_num)
        if desc:
            # Extract method signature from spec
            method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
            if method_match:
                signature = method_match.group(0)
                return f"```dafny\n{signature}\n```\n\n{desc}"
            else:
                return desc
    
    # For auxiliary methods or fallback
    return generate_auxiliary_description(method_name, task_num, spec_content)

def update_yaml_description(yaml_path: Path) -> bool:
    """Update description in a single YAML file."""
    try:
        with open(yaml_path, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        # Extract task number from filename
        filename = yaml_path.stem
        task_num = None
        
        patterns = [r'^(\d{3})-', r'^(\d{3})_', r'^(\d{1,3})-']
        for pattern in patterns:
            match = re.match(pattern, filename)
            if match:
                task_num = int(match.group(1))
                break
        
        if task_num is None:
            print(f"Could not extract task number from {filename}")
            return False
        
        # Determine if this is a main method or auxiliary
        is_main_method = '__' not in filename
        method_name = filename.split('__')[1] if '__' in filename else filename.split('-', 1)[1]
        
        # Get spec content
        spec_content = yaml_data.get('vc-spec', '')
        
        # Create improved description
        new_description = create_improved_description(task_num, method_name, spec_content, is_main_method)
        
        # Update YAML data
        yaml_data['vc-description'] = new_description
        
        # Write back in proper order
        ordered_data = {}
        for section in ['vc-preamble', 'vc-helpers', 'vc-description', 'vc-spec', 'vc-code', 'vc-postamble']:
            if section in yaml_data:
                ordered_data[section] = yaml_data[section]
        
        # Write back with literal format
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
        
        print(f"Updated description for {yaml_path.name}")
        return True
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Update descriptions in all YAML files."""
    if not YAML_DIR.exists():
        print(f"YAML directory not found: {YAML_DIR}")
        return
    
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to update")
    
    updated = 0
    for yaml_file in yaml_files:
        if update_yaml_description(yaml_file):
            updated += 1
    
    print(f"Successfully updated descriptions in {updated} out of {len(yaml_files)} files")

if __name__ == "__main__":
    main()
