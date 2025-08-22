#!/usr/bin/env python3

import json
import re
import sys
import argparse
import os
from typing import Dict, Any, List, Tuple, Set
from pathlib import Path

def dafny_default_value(typ, for_method=False):
    """Return a default value for a Dafny type."""
    typ = typ.strip()
    
    # Handle Tree datatype specifically
    if 'Tree' in typ:
        return 'Empty'
    
    if typ == 'int' or typ == 'nat':
        return '0'
    elif typ == 'real':
        return '0.0'
    elif typ == 'bool':
        return 'false'
    elif typ == 'string':
        return '""'
    elif typ.startswith('array<') or typ.startswith('seq<'):
        return '[]'
    elif typ.startswith('set<'):
        return '{}'
    elif typ.startswith('multiset<'):
        return 'multiset{}'
    else:
        # For unknown types, try to provide a reasonable default
        if 'int' in typ.lower():
            return '0'
        elif 'real' in typ.lower():
            return '0.0'
        elif 'bool' in typ.lower():
            return 'false'
        elif 'string' in typ.lower():
            return '""'
        else:
            return 'null'

def parse_return_type_from_signature(signature_line):
    """Helper function from turn_to_assume.py to parse return types."""
    if not signature_line:
        return None
    match = re.search(r'returns\s*\(([^)]*)\)', signature_line)
    if match and match.group(1):
        return f'({match.group(1).strip()})'
    match2 = re.search(r'\):\s*([^{\s]+)', signature_line)
    if match2 and match2.group(1):
        return match2.group(1).strip()
    return None

def parse_atom_info(atom_content: str) -> Dict[str, Any]:
    """Parse atom content to extract type, return type, and ensures clauses."""
    lines = atom_content.split('\n')
    atom_type = None
    return_type = None
    ensures_clauses = []
    
    # Find the first line to determine atom type
    for line in lines:
        line = line.strip()
        if line.startswith('method '):
            atom_type = 'method'
            break
        elif line.startswith('function '):
            atom_type = 'function'
            break
        elif line.startswith('ghost function '):
            atom_type = 'function'
            break
        elif line.startswith('opaque function '):
            atom_type = 'opaque function'
            break
        elif line.startswith('lemma '):
            atom_type = 'lemma'
            break
        elif line.startswith('predicate '):
            atom_type = 'predicate'
            break
        elif line.startswith('datatype '):
            atom_type = 'datatype'
            break
    
    # Extract return type and ensures clauses
    for line in lines:
        line = line.strip()
        if 'returns' in line or '):' in line:
            return_type = parse_return_type_from_signature(line)
        elif line.startswith('ensures '):
            ensures_clause = line[8:].strip()  # Remove 'ensures ' prefix
            # Remove trailing semicolon if present
            if ensures_clause.endswith(';'):
                ensures_clause = ensures_clause[:-1]
            # Don't fix implies here - let the syntax cleaning handle it properly
            ensures_clauses.append(ensures_clause)
    
    return {
        'type': atom_type,
        'return_type': return_type,
        'ensures_clauses': ensures_clauses
    }

def clean_dafny_syntax(content: str) -> str:
    """Clean up Dafny syntax by removing unnecessary semicolons and fixing common issues."""
    lines = content.split('\n')
    cleaned_lines = []
    
    for line in lines:
        # Remove unnecessary semicolons from spec clauses
        if any(line.strip().startswith(clause) for clause in ['requires', 'ensures', 'reads', 'modifies', 'decreases']):
            if line.strip().endswith(';'):
                line = line.rstrip(';')
        
        # Fix common syntax issues - be careful about implies
        # Only fix obviously malformed implies (== instead of ==>)
        if ' == ' in line and ' ==> ' not in line:
            # Check if this looks like it should be an implies
            if any(keyword in line for keyword in ['ensures', 'requires', 'assume']):
                # This might be a malformed implies, but let's be conservative
                pass
        
        # Normalize double spaces
        line = line.replace('  ', ' ')
        
        cleaned_lines.append(line)
    
    return '\n'.join(cleaned_lines)

def create_assume_body(atom_content: str) -> str:
    """Creates an assume body for a method, using assume statements for ensures clauses."""
    # Parse atom information
    atom_info = parse_atom_info(atom_content)
    atom_type = atom_info['type']
    return_type = atom_info['return_type']
    ensures_clauses = atom_info['ensures_clauses']
    
    # Only process methods
    if atom_type != 'method':
        return atom_content
    
    # For method: block with assume/return
    lines = atom_content.split('\n')
    result_lines = []
    in_body = False
    brace_count = 0
    
    for i, line in enumerate(lines):
        if not in_body:
            if '{' in line:
                brace_pos = line.find('{')
                result_lines.append(line[:brace_pos] + '{')
                in_body = True
                brace_count = 1
                
                # For methods, first assign return value, then assume ensures clauses
                if return_type:
                    # Parse return type to get variable name and assign default value
                    if return_type.startswith('(') and return_type.endswith(')'):
                        # Handle tuple return type
                        inner = return_type[1:-1]
                        parts = [p.strip() for p in inner.split(',')]
                        for part in parts:
                            var_name = part.split(':')[0].strip()
                            var_type = part.split(':')[1].strip() if ':' in part else part
                            default_val = dafny_default_value(var_type, for_method=False)
                            result_lines.append(f'    {var_name} := {default_val};')
                    else:
                        # Handle single return type
                        return_var = return_type.split(':')[0].strip()
                        result_lines.append(f'    {return_var} := {dafny_default_value(return_type, for_method=False)};')
                
                # Add assume statements for ensures clauses
                for ensures in ensures_clauses:
                    # Clean up the ensures clause
                    ensures_clean = ensures.strip()
                    # Remove any trailing semicolon if present
                    if ensures_clean.endswith(';'):
                        ensures_clean = ensures_clean[:-1]
                    # Fix common syntax issues in assume statements
                    # Replace == with ==> for implies in assume statements
                    if ' == ' in ensures_clean and ' ==> ' not in ensures_clean:
                        # This looks like it should be an implies
                        ensures_clean = ensures_clean.replace(' == ', ' ==> ')
                    result_lines.append(f'    assume {ensures_clean};')
                
                # For methods, add return statement at the end
                if return_type:
                    if return_type.startswith('(') and return_type.endswith(')'):
                        # Handle tuple return type
                        inner = return_type[1:-1]
                        parts = [p.strip() for p in inner.split(',')]
                        var_names = [part.split(':')[0].strip() for part in parts]
                        result_lines.append(f'    return {", ".join(var_names)};')
                    else:
                        # Handle single return type
                        return_var = return_type.split(':')[0].strip()
                        result_lines.append(f'    return {return_var};')
                
                if '}' in line[brace_pos+1:]:
                    result_lines.append('}')
                    in_body = False
                    brace_count = 0
            else:
                result_lines.append(line)
        else:
            for char in line:
                if char == '{':
                    brace_count += 1
                elif char == '}':
                    brace_count -= 1
                    if brace_count == 0:
                        result_lines.append('}')
                        in_body = False
                        break
    return '\n'.join(result_lines)

def create_spec_body(atom_content: str, method_name: str = None) -> str:
    """Creates a spec body for a method, replacing the body with empty braces {}."""
    # Parse atom information
    atom_info = parse_atom_info(atom_content)
    atom_type = atom_info['type']
    
    # Only process methods
    if atom_type != 'method':
        return atom_content
    
    # For all methods: replace body with empty braces
    # Removed special case for Main() methods - they should get dependencies too
    lines = atom_content.split('\n')
    result_lines = []
    in_body = False
    brace_count = 0
    
    for i, line in enumerate(lines):
        if not in_body:
            if '{' in line:
                brace_pos = line.find('{')
                result_lines.append(line[:brace_pos] + '{')
                in_body = True
                brace_count = 1
                
                if '}' in line[brace_pos+1:]:
                    result_lines.append('}')
                    in_body = False
                    brace_count = 0
            else:
                result_lines.append(line)
        else:
            for char in line:
                if char == '{':
                    brace_count += 1
                elif char == '}':
                    brace_count -= 1
                    if brace_count == 0:
                        result_lines.append('}')
                        in_body = False
                        break
    return '\n'.join(result_lines)

def get_atom_type(atom_content: str) -> str:
    """Determine the type of an atom (method, function, predicate, datatype, etc.)."""
    lines = atom_content.split('\n')
    for line in lines:
        line = line.strip()
        if line.startswith('method '):
            return 'method'
        elif line.startswith('function '):
            return 'function'
        elif line.startswith('ghost function '):
            return 'function'
        elif line.startswith('opaque function '):
            return 'opaque function'
        elif line.startswith('lemma '):
            return 'lemma'
        elif line.startswith('predicate '):
            return 'predicate'
        elif line.startswith('datatype '):
            return 'datatype'
    return 'unknown'

def process_json_file(input_file: str, output_dir: str = None) -> None:
    """
    Process a JSON file and create separate Dafny files for each method.
    """
    try:
        with open(input_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error reading {input_file}: {e}")
        return
    
    # Determine output directory if not provided
    if output_dir is None:
        # Use a common directory for all files
        output_dir = "simple_specs"
    
    # Create output directory
    os.makedirs(output_dir, exist_ok=True)
    
    # Extract atoms from either format
    atoms = {}
    if 'atoms' in data:
        # New format with skeleton
        atoms = data['atoms']
    elif 'data' in data:
        # Old format without skeleton
        atoms = data['data']
    else:
        print(f"No 'atoms' or 'data' field found in {input_file}")
        return
    
    # Find all methods
    methods = {}
    other_atoms = {}
    
    for atom_name, atom_data in atoms.items():
        if isinstance(atom_data, list) and len(atom_data) >= 2:
            atom_content = atom_data[1]
            atom_type = get_atom_type(atom_content)
            
            if atom_type == 'method':
                methods[atom_name] = atom_data
            elif atom_type in ['function', 'opaque function', 'predicate', 'datatype']:
                # Keep functions, opaque functions, predicates, and datatypes
                other_atoms[atom_name] = atom_data
            # Skip lemmas and other types
    
    print(f"Found {len(methods)} methods and {len(other_atoms)} other atoms")
    
    # Process each method
    for method_name, method_data in methods.items():
        print(f"Processing method: {method_name}")
        
        # Get dependencies for this method
        dependencies = method_data[0] if len(method_data) > 0 else []
        
        # Build the output content
        output_lines = []
        
        # Add datatypes first (they should always be included)
        for atom_name, atom_data in other_atoms.items():
            if get_atom_type(atom_data[1]) == 'datatype':
                dep_content = atom_data[1]
                output_lines.append("//ATOM")
                output_lines.append(dep_content)
                output_lines.append("")  # Empty line
        
        # Collect all dependencies recursively
        all_dependencies = set()
        to_process = list(dependencies)
        
        while to_process:
            dep_name = to_process.pop(0)
            if dep_name in all_dependencies:
                continue
            all_dependencies.add(dep_name)
            
            # If this dependency has its own dependencies, add them to the processing list
            if dep_name in other_atoms:
                dep_dependencies = other_atoms[dep_name][0] if len(other_atoms[dep_name]) > 0 else []
                for sub_dep in dep_dependencies:
                    if sub_dep not in all_dependencies:
                        to_process.append(sub_dep)
            elif dep_name in methods:
                dep_dependencies = methods[dep_name][0] if len(methods[dep_name]) > 0 else []
                for sub_dep in dep_dependencies:
                    if sub_dep not in all_dependencies:
                        to_process.append(sub_dep)
        
        # Add all collected dependencies
        for dep_name in all_dependencies:
            if dep_name in other_atoms:
                # Function, predicate, or datatype - add as //ATOM
                dep_content = other_atoms[dep_name][1]
                dep_content = clean_dafny_syntax(dep_content)
                output_lines.append("//ATOM")
                output_lines.append(dep_content)
                output_lines.append("")  # Empty line
            elif dep_name in methods:
                # Method dependency - convert to assume and add as //ATOM
                dep_content = methods[dep_name][1]
                assume_content = create_assume_body(dep_content)
                assume_content = clean_dafny_syntax(assume_content)
                output_lines.append("//ATOM")
                output_lines.append(assume_content)
                output_lines.append("")  # Empty line
        
        # Add the method itself
        method_content = method_data[1]
        # Convert the main method to spec format (empty body)
        spec_content = create_spec_body(method_content, method_name)
        spec_content = clean_dafny_syntax(spec_content)
        output_lines.append("// SPEC")
        output_lines.append(spec_content)
        
        # Write to file
        # Use original file name + method name
        base_name = os.path.splitext(os.path.basename(input_file))[0]
        output_filename = os.path.join(output_dir, f"{base_name}_{method_name}.dfy")
        with open(output_filename, 'w', encoding='utf-8') as f:
            f.write('\n'.join(output_lines))
        
        print(f"  Created: {output_filename}")
    
    print(f"All files saved to: {output_dir}")

def process_single_file(input_file: str, output_dir: str = None):
    """Process a single JSON file."""
    if not os.path.exists(input_file):
        print(f"Error: File {input_file} does not exist")
        return
    
    print(f"Processing: {input_file}")
    process_json_file(input_file, output_dir)
    print(f"✓ Successfully processed {input_file}")

def process_directory(directory_path: str, recursive: bool = False):
    """Process all JSON files in a directory."""
    if not os.path.isdir(directory_path):
        print(f"Error: Directory {directory_path} does not exist")
        return
    
    # Find all JSON files
    json_files = []
    if recursive:
        for root, dirs, files in os.walk(directory_path):
            for file in files:
                if file.endswith('.json') and not file.endswith('_simple_specs.json'):
                    json_files.append(os.path.join(root, file))
    else:
        for file in os.listdir(directory_path):
            if file.endswith('.json') and not file.endswith('_simple_specs.json'):
                json_files.append(os.path.join(directory_path, file))
    
    if not json_files:
        print(f"No JSON files found in {directory_path}")
        return
    
    print(f"Found {len(json_files)} JSON files to process")
    
    # Use a common output directory for all files
    common_output_dir = "simple_specs"
    
    successful = 0
    failed = 0
    
    for json_file in json_files:
        try:
            process_single_file(json_file, common_output_dir)
            successful += 1
        except Exception as e:
            print(f"Failed to process {json_file}: {e}")
            failed += 1
    
    print(f"\nDirectory processing complete:")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total: {len(json_files)}")
    print(f"  All files saved to: {common_output_dir}")

def main():
    parser = argparse.ArgumentParser(
        description='Turn JSON files into simple spec files - one Dafny file per method with dependencies'
    )
    parser.add_argument(
        'input_path', 
        help='Input JSON file or directory containing JSON files'
    )
    parser.add_argument(
        '--output-dir', 
        help='Output directory for generated Dafny files (default: input_file with _simple_specs suffix)'
    )
    parser.add_argument(
        '--recursive', '-r', 
        action='store_true', 
        help='Process directories recursively'
    )
    
    args = parser.parse_args()
    
    # Check if input is a directory
    if os.path.isdir(args.input_path):
        process_directory(args.input_path, args.recursive)
    else:
        # Process single file
        process_single_file(args.input_path, args.output_dir)

if __name__ == "__main__":
    main() 