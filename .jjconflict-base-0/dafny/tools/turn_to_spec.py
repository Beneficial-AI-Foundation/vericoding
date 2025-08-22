#!/usr/bin/env python3

import json
import re
import sys
import argparse
import os
from typing import Dict, Any, List, Tuple

def remove_atom_body(atom_content: str, allowed_types: set = None) -> str:
    """
    Removes the implementation body from a Dafny atom, replacing it with empty braces {}.
    Preserves the signature, requires/ensures clauses, and other specifications.
    Adds "// SPEC" comment at the top for atoms that get empty bodies.
    """
    # Check if this is a predicate - if so, leave the body unchanged
    if atom_content.strip().startswith('predicate '):
        return atom_content
    
    # Check if this is a main method - if so, leave the body unchanged
    main_match = re.search(r'method\s+main\s*\(', atom_content, re.IGNORECASE)
    if main_match:
        return atom_content
    
    # Determine atom type
    atom_type = None
    lines = atom_content.split('\n')
    for line in lines:
        line = line.strip()
        if line.startswith('method '):
            atom_type = 'method'
            break
        elif line.startswith('function '):
            atom_type = 'function'
            break
        elif line.startswith('opaque function '):
            atom_type = 'opaque function'
            break
        elif line.startswith('lemma '):
            atom_type = 'lemma'
            break
    
    # If specific types are specified and this atom type is not in the allowed list, leave unchanged
    if allowed_types and atom_type not in allowed_types:
        return atom_content
    
    # Split the content into lines
    result_lines = []
    in_body = False
    brace_count = 0
    
    for i, line in enumerate(lines):
        if not in_body:
            # Check if this line contains the start of the body
            if '{' in line:
                # Find the position of the opening brace
                brace_pos = line.find('{')
                # Add the line up to the opening brace
                result_lines.append(line[:brace_pos] + '{')
                in_body = True
                brace_count = 1
                
                # Check if the closing brace is on the same line
                if '}' in line[brace_pos+1:]:
                    result_lines.append('}')
                    in_body = False
                    brace_count = 0
            else:
                result_lines.append(line)
        else:
            # We're in the body, count braces
            for char in line:
                if char == '{':
                    brace_count += 1
                elif char == '}':
                    brace_count -= 1
                    if brace_count == 0:
                        # End of body reached
                        result_lines.append('}')
                        in_body = False
                        break
            # Don't add body lines to result
    
    # Add "// SPEC" comment at the top
    result = '\n'.join(result_lines)
    return "// SPEC \n" + result

def add_atom_comment(atom_content: str) -> str:
    """
    Adds "// ATOM" comment at the top of an atom that is not being modified.
    """
    return "// ATOM \n" + atom_content

def extract_spec_dependencies(dafny_code: str) -> List[str]:
    """
    Extract dependencies from the spec part (before the first '{').
    """
    body_start = dafny_code.find('{')
    if body_start == -1:
        return []
    spec_part = dafny_code[:body_start]
    call_pattern = r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\("
    dafny_keywords = {
        "method", "function", "lemma", "predicate", "datatype",
        "if", "then", "else", "while", "for", "return",
        "returns", "var", "in", "out", "new", "assert", "assume", "calc",
        "requires", "ensures", "reads", "modifies", "decreases",
        "old", "fresh", "allocated", "forall", "exists", "multiset",
        "array", "seq", "set", "map", "int", "bool", "char", "string",
        "real", "nat", "object", "null", "true", "false"
    }
    calls = set(re.findall(call_pattern, spec_part))
    return [c for c in calls if c not in dafny_keywords]

def process_json_file(input_file: str, spec_output_file: str = None, allowed_types: set = None) -> Dict[str, Any]:
    """
    Process a JSON file containing Dafny atoms and create a spec version with empty bodies.
    """
    try:
        with open(input_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error reading {input_file}: {e}")
        return {}
    
    # Determine output filename if not provided
    if spec_output_file is None:
        base_name = os.path.splitext(input_file)[0]
        spec_output_file = f"{base_name}_spec.json"
    
    # Process atoms to remove bodies
    if 'atoms' in data:
        processed_atoms = {}
        for atom_name, atom_data in data['atoms'].items():
            if isinstance(atom_data, list) and len(atom_data) >= 2:
                # Extract the atom content (second element in the list)
                atom_content = atom_data[1]
                
                # Check if this atom should be modified
                should_modify = False
                if atom_content.strip().startswith('predicate '):
                    should_modify = False
                else:
                    # Check if this is a main method - if so, don't modify
                    main_match = re.search(r'method\s+main\s*\(', atom_content, re.IGNORECASE)
                    if main_match:
                        should_modify = False
                    else:
                        # Determine atom type
                        atom_type = None
                        lines = atom_content.split('\n')
                        for line in lines:
                            line = line.strip()
                            if line.startswith('method '):
                                atom_type = 'method'
                                break
                            elif line.startswith('function '):
                                atom_type = 'function'
                                break
                            elif line.startswith('opaque function '):
                                atom_type = 'opaque function'
                                break
                            elif line.startswith('lemma '):
                                atom_type = 'lemma'
                                break
                        
                        # Check if this type should be modified
                        if not allowed_types or atom_type in allowed_types:
                            should_modify = True
                
                if should_modify:
                    # Remove the body and add "// SPEC" comment
                    processed_content = remove_atom_body(atom_content, allowed_types)
                    # Update dependencies to only those in the spec part
                    new_deps = extract_spec_dependencies(atom_content)
                    processed_atoms[atom_name] = [new_deps, processed_content] + atom_data[2:]
                else:
                    # Add "// ATOM" comment for atoms that are not modified
                    processed_content = add_atom_comment(atom_content)
                    processed_atoms[atom_name] = [atom_data[0], processed_content] + atom_data[2:]
            else:
                # Keep as is if not in expected format
                processed_atoms[atom_name] = atom_data
        
        # Create new data structure
        spec_data = data.copy()
        spec_data['atoms'] = processed_atoms
        
        # Save to file
        try:
            with open(spec_output_file, 'w', encoding='utf-8') as f:
                json.dump(spec_data, f, indent=2)
            print(f"Spec JSON saved to: {spec_output_file}")
        except Exception as e:
            print(f"Error writing {spec_output_file}: {e}")
            return {}
        
        return spec_data
    else:
        print(f"No 'atoms' field found in {input_file}")
        return {}

def process_single_file(input_file: str, spec_output_file: str = None, allowed_types: set = None):
    """
    Process a single JSON file to create spec version.
    """
    if not os.path.exists(input_file):
        print(f"Error: File {input_file} does not exist")
        return
    
    print(f"Processing: {input_file}")
    result = process_json_file(input_file, spec_output_file, allowed_types)
    if result:
        print(f"✓ Successfully processed {input_file}")
    else:
        print(f"✗ Failed to process {input_file}")

def process_directory(directory_path: str, recursive: bool = False, allowed_types: set = None):
    """
    Process all JSON files in a directory to create spec versions.
    """
    if not os.path.isdir(directory_path):
        print(f"Error: Directory {directory_path} does not exist")
        return
    
    # Find all JSON files
    json_files = []
    if recursive:
        for root, dirs, files in os.walk(directory_path):
            for file in files:
                if file.endswith('.json') and not file.endswith('_spec.json'):
                    json_files.append(os.path.join(root, file))
    else:
        for file in os.listdir(directory_path):
            if file.endswith('.json') and not file.endswith('_spec.json'):
                json_files.append(os.path.join(directory_path, file))
    
    if not json_files:
        print(f"No JSON files found in {directory_path}")
        return
    
    print(f"Found {len(json_files)} JSON files to process")
    
    successful = 0
    failed = 0
    
    for json_file in json_files:
        try:
            process_single_file(json_file, allowed_types=allowed_types)
            successful += 1
        except Exception as e:
            print(f"Failed to process {json_file}: {e}")
            failed += 1
    
    print(f"\nDirectory processing complete:")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total: {len(json_files)}")

def main():
    parser = argparse.ArgumentParser(description='Turn Dafny atoms in JSON files to spec version with empty bodies')
    parser.add_argument('input_path', help='Input JSON file or directory containing JSON files')
    parser.add_argument('--spec-output', help='Output file path for spec version (default: input_file with _spec suffix)')
    parser.add_argument('--recursive', '-r', action='store_true', help='Process directories recursively')
    parser.add_argument('--methods', action='store_true', help='Only modify method atoms')
    parser.add_argument('--functions', action='store_true', help='Only modify function and opaque function atoms')
    parser.add_argument('--lemmas', action='store_true', help='Only modify lemma atoms')
    
    args = parser.parse_args()
    
    # Determine which atom types to modify
    allowed_types = set()
    if args.methods:
        allowed_types.add('method')
    if args.functions:
        allowed_types.add('function')
        allowed_types.add('opaque function')
    if args.lemmas:
        allowed_types.add('lemma')
    
    # If no specific types are specified, allow all non-predicate types (backward compatibility)
    if not allowed_types:
        allowed_types = {'method', 'function', 'opaque function', 'lemma'}
    
    print(f"Modifying atom types: {', '.join(sorted(allowed_types))}")
    
    # Check if input is a directory
    if os.path.isdir(args.input_path):
        process_directory(args.input_path, args.recursive, allowed_types)
    else:
        # Process single file
        process_single_file(args.input_path, args.spec_output, allowed_types)

if __name__ == "__main__":
    main() 