#!/usr/bin/env python3

import re
from pathlib import Path
import yaml

# Directory
YAML_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/dafny/humaneval/yaml")

def analyze_method_spec(spec_content: str, method_name: str) -> str:
    """Analyze the method specification to create an informative description."""
    
    # Extract method signature
    method_match = re.search(r'method\s+(\w+)\s*\([^)]*\)\s*(?:returns\s*\([^)]*\))?', spec_content)
    if not method_match:
        return f"Auxiliary method {method_name}."
    
    signature = method_match.group(0).strip()
    
    # Extract requires and ensures clauses
    requires_matches = re.findall(r'requires\s+([^/\n]+)', spec_content)
    ensures_matches = re.findall(r'ensures\s+([^/\n]+)', spec_content)
    
    # Create description based on method name and spec content
    description_parts = []
    
    # Method-specific analysis
    if 'sort' in method_name.lower():
        if 'SortSeq' in method_name:
            description_parts.append("Sort a sequence according to a custom ordering relation.")
        elif 'sorted' in method_name.lower():
            description_parts.append("Check if a sequence is sorted according to specific criteria.")
        else:
            description_parts.append("Sort elements using a specific algorithm or criteria.")
    
    elif 'count' in method_name.lower():
        if ensures_matches:
            for ensure in ensures_matches[:1]:  # Take first ensure for context
                if 'set' in ensure or '|' in ensure:
                    description_parts.append("Count elements that satisfy specific conditions using set comprehension.")
                else:
                    description_parts.append("Count occurrences of elements or patterns.")
        else:
            description_parts.append("Count elements based on specific criteria.")
    
    elif 'reverse' in method_name.lower():
        description_parts.append("Reverse the order of elements in a sequence or string.")
    
    elif 'sum' in method_name.lower():
        if 'chars' in method_name.lower():
            description_parts.append("Calculate the sum of character lengths in a sequence of strings.")
        elif 'elements' in method_name.lower():
            description_parts.append("Sum elements that meet specific numerical criteria.")
        else:
            description_parts.append("Calculate sum of elements according to specific rules.")
    
    elif 'get' in method_name.lower():
        if 'row' in method_name.lower():
            description_parts.append("Retrieve positions or elements from a 2D structure.")
        else:
            description_parts.append("Retrieve elements that match specific criteria.")
    
    elif method_name.startswith('is_') or method_name.endswith('_check'):
        description_parts.append("Check a boolean condition or property.")
    
    elif 'filter' in method_name.lower():
        description_parts.append("Filter elements based on specific conditions.")
    
    elif 'parse' in method_name.lower():
        if 'paren' in method_name.lower():
            description_parts.append("Parse parentheses structures according to nesting rules.")
        else:
            description_parts.append("Parse input according to specific format rules.")
    
    elif 'select' in method_name.lower():
        if 'digits' in method_name.lower():
            description_parts.append("Select elements based on digit count constraints.")
        else:
            description_parts.append("Select elements that meet specific criteria.")
    
    elif 'generate' in method_name.lower():
        description_parts.append("Generate elements according to specific rules or constraints.")
    
    elif 'encode' in method_name.lower() or 'decode' in method_name.lower():
        description_parts.append("Transform strings using encoding/decoding algorithms.")
    
    elif 'max' in method_name.lower() or 'min' in method_name.lower():
        description_parts.append("Find maximum or minimum elements based on specific criteria.")
    
    else:
        # Generic analysis based on return type and parameters
        if 'returns' in signature:
            return_match = re.search(r'returns\s*\([^)]*\)', signature)
            if return_match:
                return_type = return_match.group(0)
                if 'bool' in return_type:
                    description_parts.append("Check a condition and return a boolean result.")
                elif 'seq' in return_type:
                    description_parts.append("Process input and return a sequence of results.")
                elif 'int' in return_type or 'nat' in return_type:
                    description_parts.append("Calculate and return a numeric result.")
                else:
                    description_parts.append(f"Process input and return result according to specification.")
    
    # Add context from ensures clauses if available and informative
    if ensures_matches and not description_parts:
        first_ensure = ensures_matches[0].strip()
        if len(first_ensure) < 100:  # Only if it's concise
            description_parts.append(f"Ensure that {first_ensure.lower()}.")
    
    # Fallback
    if not description_parts:
        description_parts.append(f"Auxiliary method for {method_name} functionality.")
    
    return ' '.join(description_parts)

def should_improve_description(description: str) -> bool:
    """Check if description needs improvement (too generic)."""
    generic_phrases = [
        "according to specific criteria",
        "Implement according to the specification",
        "related to HumanEval task",
        "Auxiliary method",
        "HumanEval task:"
    ]
    
    return any(phrase in description for phrase in generic_phrases)

def update_yaml_file(yaml_path: Path) -> bool:
    """Update description in a single YAML file if it's too generic."""
    try:
        with open(yaml_path, 'r') as f:
            yaml_data = yaml.safe_load(f)
        
        # Get current description
        current_description = yaml_data.get('vc-description', '')
        if not current_description:
            return False
        
        # Check if description needs improvement
        if not should_improve_description(str(current_description)):
            return False
        
        # Extract method name from filename
        filename = yaml_path.stem
        method_name = filename.split('__')[1] if '__' in filename else filename.split('-', 1)[1]
        
        # Get spec content
        spec_content = yaml_data.get('vc-spec', '')
        if not spec_content:
            return False
        
        # Generate better description
        better_description = analyze_method_spec(spec_content, method_name)
        
        # Extract function signature from current description
        lines = str(current_description).split('\n')
        signature_line = None
        for line in lines:
            if line.strip().startswith('function_signature:'):
                signature_line = line.strip()
                break
        
        # Create new description
        if signature_line:
            new_description = f"{signature_line}\n{better_description}"
        else:
            new_description = better_description
        
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
        
        print(f"Improved description for {yaml_path.name}")
        return True
        
    except Exception as e:
        print(f"Error updating {yaml_path.name}: {e}")
        return False

def main():
    """Improve generic descriptions in auxiliary method YAML files."""
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
    
    print(f"Successfully improved descriptions in {updated} auxiliary method files")

if __name__ == "__main__":
    main()
