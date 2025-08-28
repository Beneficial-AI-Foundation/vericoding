#!/usr/bin/env python3

import re
from pathlib import Path
import yaml

# Directories
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")
SOURCE_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/source")

def extract_functions_from_source(source_file: Path) -> dict[str, str]:
    """Extract all function definitions from a source file."""
    if not source_file.exists():
        return {}
    
    content = source_file.read_text()
    functions = {}
    
    # Find function definitions (including type definitions)
    function_pattern = r'((?:function|type)\s+\w+[^{]*\{[^}]*\})'
    
    matches = re.finditer(function_pattern, content, re.MULTILINE | re.DOTALL)
    for match in matches:
        func_def = match.group(0).strip()
        # Extract function name
        name_match = re.search(r'(?:function|type)\s+(\w+)', func_def)
        if name_match:
            func_name = name_match.group(1)
            functions[func_name] = func_def
    
    return functions

def find_referenced_identifiers(text: str) -> set[str]:
    """Find all identifiers that might be function calls in the text."""
    # Look for identifiers followed by parentheses or used in expressions
    identifiers = set()
    
    # Function calls: identifier(
    func_calls = re.findall(r'(\w+)\s*\(', text)
    identifiers.update(func_calls)
    
    # Type references and other identifiers
    type_refs = re.findall(r'\b([A-Z]\w*)\b', text)
    identifiers.update(type_refs)
    
    return identifiers

def fix_yaml_file(yaml_file: Path, source_functions: dict[str, str]) -> bool:
    """Fix a YAML file by adding missing function definitions."""
    try:
        with open(yaml_file, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        # Get the spec content to analyze for missing functions
        spec_content = yaml_data.get('vc-spec', '')
        preamble_content = yaml_data.get('vc-preamble', '')
        
        # Find referenced identifiers
        all_content = spec_content + preamble_content
        referenced_ids = find_referenced_identifiers(all_content)
        
        # Find which functions are missing
        missing_functions = []
        for func_name in referenced_ids:
            if func_name in source_functions:
                # Check if function is already in preamble
                if func_name not in preamble_content:
                    missing_functions.append(source_functions[func_name])
        
        if missing_functions:
            # Add missing functions to preamble
            current_preamble = yaml_data.get('vc-preamble', '').strip()
            if current_preamble:
                new_preamble = current_preamble + '\n\n' + '\n\n'.join(missing_functions)
            else:
                new_preamble = '\n\n'.join(missing_functions)
            
            yaml_data['vc-preamble'] = new_preamble
            
            # Write back the YAML
            output_lines = []
            ordered_sections = ['vc-preamble', 'vc-helpers', 'vc-description', 'vc-spec', 'vc-code', 'vc-postamble']
            
            for section_name in ordered_sections:
                if section_name in yaml_data:
                    content = yaml_data[section_name]
                    output_lines.append(f"{section_name}: |-")
                    if content and str(content).strip():
                        for line in str(content).split('\n'):
                            output_lines.append(f"  {line}")
                    else:
                        output_lines.append("")
                    output_lines.append("")
            
            with open(yaml_file, 'w') as f:
                f.write('\n'.join(output_lines).rstrip() + '\n')
            
            print(f"Fixed {yaml_file.name} - added {len(missing_functions)} functions")
            return True
        
        return False
        
    except Exception as e:
        print(f"Error fixing {yaml_file.name}: {e}")
        return False

def main():
    """Fix missing function definitions in YAML files."""
    
    # Process each failing file specifically
    failing_files = [
        "026-remove_duplicates__count.yaml",
        "026-remove_duplicates__remove_duplicates.yaml",
        "059-largest-prime-factor__is_prime.yaml", 
        "059-largest-prime-factor__largest_prime_factor.yaml",
        "065-circular_shift__circular_shift.yaml",
        "065-circular_shift__reverse.yaml",
        "074-total_match__SumChars.yaml",
        "074-total_match__TotalMatch.yaml",
        "087-get_row__get_row.yaml",
        "087-get_row__SortSeq.yaml", 
        "122-add_elements__select_at_most_two_digits.yaml",
        "122-add_elements__SumElementsWithAtMostTwoDigits.yaml"
    ]
    
    fixed_count = 0
    for yaml_filename in failing_files:
        yaml_file = YAML_DIR / yaml_filename
        if not yaml_file.exists():
            print(f"YAML file not found: {yaml_filename}")
            continue
        
        # Get corresponding source file
        base_name = yaml_filename.split('__')[0]  # Get the base name before __
        source_file = SOURCE_DIR / f"{base_name}.dfy"
        
        if not source_file.exists():
            print(f"Source file not found: {source_file}")
            continue
        
        # Extract functions from source
        source_functions = extract_functions_from_source(source_file)
        
        if fix_yaml_file(yaml_file, source_functions):
            fixed_count += 1
    
    print(f"\nFixed {fixed_count} YAML files with missing function definitions")

if __name__ == "__main__":
    main()
