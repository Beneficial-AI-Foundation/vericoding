#!/usr/bin/env python3

import re
from pathlib import Path
import yaml

# Directory
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")

def extract_spec_conditions(spec_content: str) -> tuple[list[str], list[str]]:
    """Extract requires and ensures clauses from method specification."""
    requires = []
    ensures = []
    
    # Extract requires clauses
    requires_matches = re.findall(r'requires\s+([^/\n]+)', spec_content, re.MULTILINE)
    for req in requires_matches:
        requires.append(req.strip())
    
    # Extract ensures clauses
    ensures_matches = re.findall(r'ensures\s+([^/\n]+)', spec_content, re.MULTILINE)
    for ens in ensures_matches:
        ensures.append(ens.strip())
    
    return requires, ensures

def interpret_condition(condition: str, is_requires: bool) -> str:
    """Interpret a requires or ensures clause into natural language."""
    condition = condition.strip()
    
    # Common patterns and their interpretations
    interpretations = []
    
    # Cube root specific
    if 'cube(r) <= N < cube(r + 1)' in condition:
        interpretations.append("the result r is the largest integer such that r³ ≤ N < (r+1)³")
    elif 'cube(r) <= N' in condition:
        interpretations.append("r³ ≤ N")
    elif 'r <= N' in condition:
        interpretations.append("the result is at most N")
    
    # Palindrome related
    elif 'is_palindrome' in condition:
        if '!' in condition:
            interpretations.append("the result is not a palindrome")
        else:
            interpretations.append("the result is a palindrome")
    
    # Count related
    elif '|set' in condition and 'x in a' in condition:
        interpretations.append("returns the count of occurrences of x in sequence a")
    elif 'cnt ==' in condition:
        interpretations.append("returns the correct count")
    
    # Sum related
    elif 'sum ==' in condition and 'sum_chars_rec' in condition:
        interpretations.append("returns the sum of character lengths in all strings")
    elif 'sum' in condition and 'length' in condition:
        interpretations.append("sums the lengths of elements")
    
    # Sorting related
    elif 'sorted' in condition and 'multiset' in condition:
        interpretations.append("returns a sorted permutation of the input")
    elif 'sorted' in condition and 'forall' in condition:
        interpretations.append("the result is sorted according to the ordering relation")
    elif 'SortSeqPred' in condition:
        interpretations.append("elements are sorted according to a custom predicate")
    
    # Encoding/Decoding
    elif 'decode_cyclic' in condition and 'encode_cyclic' in condition:
        interpretations.append("decoding the encoded string returns the original")
    elif 'encode_shift' in condition and 'decode_shift' in condition:
        interpretations.append("decoding the encoded string returns the original")
    
    # Filtering
    elif 'checkSubstring' in condition:
        interpretations.append("filters elements containing the substring")
    elif 'select_at_most_two_digits' in condition:
        interpretations.append("selects only numbers with at most two digits")
    
    # Boolean conditions
    elif condition.startswith('r ==>'):
        right_side = condition.split('==>', 1)[1].strip()
        interpretations.append(f"if true, then {interpret_condition(right_side, False)}")
    elif condition.startswith('!r ==>'):
        right_side = condition.split('==>', 1)[1].strip()
        interpretations.append(f"if false, then {interpret_condition(right_side, False)}")
    
    # Existence conditions
    elif 'exists' in condition:
        if 'cube(r)' in condition:
            interpretations.append("there exists an integer r such that N = r³")
        else:
            interpretations.append("there exists a value satisfying the condition")
    
    # Universal conditions
    elif 'forall' in condition:
        if 'cube(r)' in condition and '!=' in condition:
            interpretations.append("no integer r satisfies N = r³")
        elif 'sorted' in condition:
            interpretations.append("all adjacent elements are in order")
        else:
            interpretations.append("the condition holds for all values")
    
    # Length/size conditions
    elif '|' in condition and 'length' not in condition:
        if '==' in condition:
            interpretations.append("returns the correct size/count")
        elif '<=' in condition:
            interpretations.append("the size is bounded")
    
    # Sequence membership
    elif ' in ' in condition and 'seq' in condition:
        interpretations.append("elements belong to the sequence")
    
    # Generic numeric conditions
    elif '>=' in condition:
        interpretations.append("the result is at least the specified value")
    elif '<=' in condition:
        interpretations.append("the result is at most the specified value")
    elif '==' in condition:
        interpretations.append("returns the correct value")
    
    # Return original condition if no interpretation found
    if not interpretations:
        # Clean up the condition for readability
        clean_condition = condition.replace('|', 'size of ').replace('==', 'equals')
        if is_requires:
            interpretations.append(f"requires {clean_condition}")
        else:
            interpretations.append(f"ensures {clean_condition}")
    
    return ', '.join(interpretations)

def create_description_from_spec(spec_content: str, method_name: str) -> str:
    """Create description based on method specification."""
    
    # Extract method signature
    method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
    if not method_match:
        return f"Auxiliary method {method_name}."
    
    signature = method_match.group(0).strip()
    
    # Extract conditions
    requires, ensures = extract_spec_conditions(spec_content)
    
    description_parts = []
    
    # Add purpose based on method name
    purpose_map = {
        'cube_root': 'Find the integer cube root',
        'count': 'Count occurrences',
        'SortSeq': 'Sort a sequence', 
        'sort': 'Sort elements',
        'sum': 'Calculate sum',
        'filter': 'Filter elements',
        'encode': 'Encode data',
        'decode': 'Decode data',
        'reverse': 'Reverse order',
        'check': 'Check condition',
        'is_': 'Check if condition holds',
        'get': 'Retrieve elements',
        'generate': 'Generate elements',
        'select': 'Select elements',
        'parse': 'Parse input'
    }
    
    purpose = None
    for key, desc in purpose_map.items():
        if key in method_name.lower():
            purpose = desc
            break
    
    if not purpose:
        purpose = "Process input"
    
    description_parts.append(f"{purpose}.")
    
    # Add requires conditions
    if requires:
        req_descriptions = []
        for req in requires:
            interpreted = interpret_condition(req, True)
            req_descriptions.append(interpreted)
        if req_descriptions:
            description_parts.append(f"Requires: {'; '.join(req_descriptions)}.")
    
    # Add ensures conditions  
    if ensures:
        ens_descriptions = []
        for ens in ensures:
            interpreted = interpret_condition(ens, False)
            ens_descriptions.append(interpreted)
        if ens_descriptions:
            description_parts.append(f"Ensures: {'; '.join(ens_descriptions)}.")
    
    return ' '.join(description_parts)

def update_yaml_file(yaml_path: Path) -> bool:
    """Update description in a single YAML file with spec-based description."""
    try:
        with open(yaml_path, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        # Get current description
        current_description = yaml_data.get('vc-description', '')
        if not current_description:
            return False
        
        # Extract function signature from current description
        lines = str(current_description).split('\n')
        signature_line = None
        for line in lines:
            if line.strip().startswith('function_signature:'):
                signature_line = line.strip()
                break
        
        if not signature_line:
            return False
        
        # Extract method name from filename
        filename = yaml_path.stem
        method_name = filename.split('__')[1] if '__' in filename else filename.split('-', 1)[1]
        
        # Get spec content
        spec_content = yaml_data.get('vc-spec', '')
        if not spec_content:
            return False
        
        # Generate spec-based description
        spec_description = create_description_from_spec(spec_content, method_name)
        
        # Create new description
        new_description = f"{signature_line}\n{spec_description}"
        
        # Update YAML data
        yaml_data['vc-description'] = new_description
        
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
        
        print(f"Updated spec-based description for {yaml_path.name}")
        return True
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Create spec-based descriptions for auxiliary method YAML files."""
    if not YAML_DIR.exists():
        print(f"YAML directory not found: {YAML_DIR}")
        return
    
    # Focus on auxiliary methods (files with __ in name)
    yaml_files = [f for f in YAML_DIR.glob("*.yaml") if '__' in f.name]
    print(f"Found {len(yaml_files)} auxiliary method files to process")
    
    updated = 0
    for yaml_file in yaml_files:
        if update_yaml_file(yaml_file):
            updated += 1
    
    print(f"Successfully updated descriptions in {updated} auxiliary method files")

if __name__ == "__main__":
    main()
