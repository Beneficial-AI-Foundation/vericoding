#!/usr/bin/env python3

# Max Tegmark, March 25 2025

import re
from typing import List, Dict, Tuple
import json
import sys
import os
import argparse

# Get the filename from CLI arguments
if len(sys.argv) < 2:
    print(json.dumps({"error": "Missing filename argument"}))
    sys.exit(1)

def loadrawtxt(filename):
    # Loads a text file as a raw string, preserving all characters 
    # (including backslashes) exactly as-is.
    with open(filename,'r',encoding='utf-8') as f: return f.read()

# Below is a simple Python solution that takes a string of Dafny code, 
# looks for a single **method** definition, and then finds all the function calls 
# (i.e., identifiers followed immediately by a parenthesis) in that method body. 
# It also filters out common Dafny keywords so they aren't mistaken for function names. 
# **Note**: This approach uses a naive regular expression and a list of hard-coded Dafny keywords to exclude. 
# In more complex Dafny code—especially with names that clash with keywords, 
# multiple methods, or advanced language features—you'll likely need a more sophisticated parser. 
def extract_dafny_function_calls(dafny_code:str) -> set:
    """
    Extracts a set of the names of all functions (or methods) that the given
    Dafny method depends on, based on simple identifier matching.
    """
    # Regex to match something that looks like an identifier followed by '('
    #   \b          : word boundary
    #   ([a-zA-Z_][a-zA-Z0-9_]*) : identifier capture group
    #   \s*\(       : optional whitespace followed by '('
    call_pattern = r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\("

    # Known Dafny keywords and built-ins we want to exclude
    dafny_keywords = {
        "method", "function", "lemma", "predicate",
        "if", "then", "else", "while", "for", "return",
        "returns", "var", "in", "out", "new", "assert", "assume", "calc"
    }

    # Try to locate the body of the first "method" in the code.
    # We do this by finding "method" up to the matching braces.
    # In real scenarios, you might have to handle nested braces or multiple methods.
    # Below is a simplistic approach that captures everything from
    # `method ... {` up to the final `}` at the same nesting level.
    method_body_pattern = r"method\s+[^{]+\{(.*?)\}"
    method_body_match = re.search(method_body_pattern, dafny_code, re.DOTALL)

    if not method_body_match:
        # If we can't find a method body, return an empty set
        return set()

    method_body = method_body_match.group(1)

    # Find all candidates that look like function calls in the method body
    candidates = re.findall(call_pattern, method_body)

    # Filter out the known Dafny keywords
    function_calls = {c for c in candidates if c not in dafny_keywords}
    function_calls = candidates
    return function_calls

dafny_method_examle = """
    method M(x:int) returns (y:int) 
    {
        var z := f(x + 1);
        if z > 0 {
            z := h(z);
        }
        return g(z);
    }
"""

dafny_method_examle = r"""
    method M(x: int) returns (y: int)
      requires F(x)
      ensures G(x)
    {
        var z := H(x + 1);
        if z > 0 {
            z := I(z);
        }
        return J(z);
    }
    """

# Please write me a Python program that reads a string containing a Dafny program, 
# and partitions it into a list of strings, each containing only a single method, 
# function, lemma, etc. preceded by any comments.
def partition_dafny_definitions(dafny_code: str) -> List[str]:    
    """
    Splits 'dafny_code' into top-level definitions (method, function, lemma, predicate, datatype).
    Ensures that any consecutive '//' comment or blank lines *immediately preceding*
    a definition are included *with that definition*, rather than the previous one.
    Returns a list of definition strings.
    """
    # We'll work line by line
    lines = dafny_code.splitlines(keepends=False)
    definition_pattern = re.compile(r'^[ \t]*(?:ghost\s+|opaque\s+)?(method|function|lemma|predicate|datatype)\b')
    definitions = []
    current_def = []             # lines for the currently active definition
    pending_comment_block = []   # blank/comment lines not yet assigned to any definition
    brace_count = 0              # track nested braces for datatypes
    in_datatype = False          # track if we're inside a datatype definition

    def finish_current_def():
        """Helper: finalize the current definition and store it if it's nonempty."""
        if current_def:
            definition_text = "\n".join(current_def).rstrip()

            # Clean up stray Markdown code block delimiters
            if definition_text.startswith("```"):
                definition_text = definition_text.lstrip("`").lstrip()
            if definition_text.endswith("```"):
                definition_text = definition_text.rstrip("`").rstrip()

            definition_text += "\n"
            definitions.append(definition_text)

    have_current_def = False  # Whether we've started any definition yet

    for line in lines:
        # Check if this line starts a new definition
        if definition_pattern.match(line):
            # Check if we're currently inside a datatype definition
            if in_datatype and brace_count > 0:
                # We're inside a datatype, so this is a nested definition
                # Just add it to the current definition
                current_def.append(line)
                # Update brace count for the nested definition
                brace_count += line.count('{') - line.count('}')
                if brace_count == 0:
                    in_datatype = False
            else:
                # We found a new top-level definition: finish the old one (if any)
                finish_current_def()
                current_def = []
                brace_count = 0
                in_datatype = False

                # Start the new definition with any pending comment lines plus this line
                current_def.extend(pending_comment_block)
                pending_comment_block.clear()

                current_def.append(line)
                have_current_def = True
                
                # Check if this is a datatype definition
                if 'datatype' in line:
                    in_datatype = True
                    brace_count = line.count('{') - line.count('}')
        else:
            # Not a new definition line
            if is_comment_or_blank(line):
                # Stash it in pending_comment_block
                # (we'll attach it to *the next* definition if it appears,
                #  or else to the current definition if a code line appears)
                pending_comment_block.append(line)
            else:
                # It's a code (non-comment) line
                # If we have a current definition, let's attach the pending comments to it
                # and then add this code line.
                if have_current_def:
                    current_def.extend(pending_comment_block)
                    pending_comment_block.clear()
                    current_def.append(line)
                    
                    # Update brace count if we're in a datatype
                    if in_datatype:
                        brace_count += line.count('{') - line.count('}')
                        if brace_count == 0:
                            in_datatype = False
                else:
                    # We have no definition yet, so these code lines come before any def.
                    # Dafny typically doesn't have "top-level code" like that, but if it does,
                    # we'll just ignore or store them somewhere. For simplicity, do nothing.
                    pass

    # End of file: finish the last definition if we have one
    finish_current_def()
    return definitions

def is_comment_or_blank(line: str) -> bool:
    """
    Returns True if 'line' is empty/whitespace, or is a single-line comment
    (leading spaces optional) that starts with '//'.
    """
    stripped = line.strip()
    if not stripped:
        return True  # blank line
    if stripped.startswith("//"):
        return True
    return False

example_code = r"""
    // This function calculates something
    function F(x: int): int
      requires x > 0
      ensures F(x) > 1

    // Here's a method:
    // with multiple lines of commentary
    method M(x: int) returns (y: int) 
      requires F(x) > 0
    {
        var z := G(x + 1);
        return H(z);
    }

    // Next up is a lemma
    lemma L()
    {
      // Some proof here
    }
    """

def partition_demo():
    filename = "bignum.dfy"
    example_code = loadrawtxt(filename)
    parts = partition_dafny_definitions(example_code)
    for i, part in enumerate(parts, start=1):
        print(f"--- Definition #{i} ---")
        print(part)
        print()

#partition_demo()
#######################################################################################
#######################################################################################


# Write a Python function taking as input a string containing a Dafny 
# method, function, lemma or predicate,  returning only its name
def definition_name(definition_str: str) -> str:
    """
    Given a string that contains exactly one Dafny definition
    (method, function, lemma, predicate, or datatype), return its name (identifier).
    Returns an empty string if no name can be found.
    """
    # Split into lines and find the first line that contains a definition
    lines = definition_str.split('\n')
    for line in lines:
        # Look for a line that starts with optional whitespace and contains a definition
        pattern = re.compile(r'^[ \t]*(?:ghost\s+|opaque\s+)?(?:method|function|lemma|predicate|datatype)\s+([a-zA-Z_][a-zA-Z0-9_]*)')
        match = pattern.search(line)
        if match:
            return match.group(1)
    
    return ""

def get_method_body(dafny_code: str) -> str:
    """
    Locates the first 'method ... {' in the code and returns everything
    inside its matching braces, accounting for nested '{' and '}'.
    Returns an empty string if no method body is found.
    """
    # Find the 'method' declaration plus the '{'
    # This pattern looks for something like: method M(...) {
    method_decl = re.search(r"method\s+\w+[^{]*\{", dafny_code)
    if not method_decl:
        return ""
    # Start scanning right after the '{' we just matched
    start_index = method_decl.end()  # position after the '{'
    brace_count = 1
    i = start_index
    # Scan forward, counting matching '{' and '}'
    while i < len(dafny_code) and brace_count > 0:
        if dafny_code[i] == '{':
            brace_count += 1
        elif dafny_code[i] == '}':
            brace_count -= 1
        i += 1
    # i is now 1 character past the matching '}', so the method body is:
    return dafny_code[start_index : i - 1]

def extract_dafny_function_calls(dafny_code: str) -> set:
    """
    Extracts a set of the names of all calls (identifiers followed by '(')
    in the *first* Dafny method definition found in 'dafny_code'.
    """
    method_body = get_method_body(dafny_code)
    if not method_body:
        return set()
    # A naive pattern for "identifier("
    call_pattern = r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\("
    return set(re.findall(call_pattern, method_body))

def get_full_method_snippet(dafny_code: str) -> str:
    """
    Finds the first 'method' definition in 'dafny_code' and returns
    the entire snippet from the 'method' keyword through the matching
    closing brace '}' (handling nested braces). Includes any specifications
    before the brace and the entire body after the brace.
    If no method is found, returns an empty string.
    """
    # Step 1: Locate the start of the "method" keyword
    start_match = re.search(r"\bmethod\b", dafny_code)
    if not start_match:
        return ""
    method_start = start_match.start()
    # Step 2: Find the first '{' after this point
    brace_index = dafny_code.find("{", method_start)
    if brace_index == -1:
        # No opening brace found
        return ""
    # Step 3: Manually match braces to find where the method ends
    brace_count = 1
    i = brace_index + 1  # start scanning after the first '{'
    while i < len(dafny_code) and brace_count > 0:
        if dafny_code[i] == '{':
            brace_count += 1
        elif dafny_code[i] == '}':
            brace_count -= 1
        i += 1
    # i is now 1 character past the matching '}', or end of file if not matched fully
    # The full method snippet is from 'method_start' up to 'i'
    return dafny_code[method_start : i]

def get_full_definition_snippet(dafny_code: str) -> str:
    """
    Finds the first top-level Dafny definition (method/function/lemma/predicate)
    and returns the full block, including its body (from keyword to matching '}').
    """
    match = re.search(r'\b(?:ghost\s+)?(method|function|lemma|predicate)\b', dafny_code)
    if not match:
        return ""

    start = match.start()

    brace_index = dafny_code.find('{', start)
    if brace_index == -1:
        return ""

    brace_count = 1
    i = brace_index + 1
    while i < len(dafny_code) and brace_count > 0:
        if dafny_code[i] == '{':
            brace_count += 1
        elif dafny_code[i] == '}':
            brace_count -= 1
        i += 1

    return dafny_code[start:i]

# def dafny_dependencies(dafny_code: str) -> set:
#     """
#     Extracts a set of the names of all function-like calls
#     (identifiers followed by '(') found in the first Dafny method
#     (including its specs, e.g., requires/ensures).
#     """
#     method_snippet = get_full_method_snippet(dafny_code)
#     if not method_snippet:
#         return set()

#     # A naive pattern: one or more letters/digits/underscore, possibly
#     # with spaces, followed by '('
#     call_pattern = r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\("
    
#     return set(re.findall(call_pattern, method_snippet))

def dafny_dependencies(dafny_code: str) -> set:
    """
    Extracts a set of all identifiers used in function/method calls inside
    the first Dafny top-level definition (method, function, etc.).
    """
    snippet = get_full_definition_snippet(dafny_code)
    if not snippet:
        return set()

    call_pattern = r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\("
    return set(re.findall(call_pattern, snippet))

def definition_type(definition_str: str) -> str:
    """
    Returns the full type of a Dafny definition, such as:
    'function', 'opaque function', 'ghost method', 'datatype', etc.
    """
    # Split into lines and find the first line that contains a definition
    lines = definition_str.split('\n')
    for line in lines:
        # Look for a line that starts with optional whitespace and contains a definition
        pattern = re.compile(r'^[ \t]*(ghost\s+|opaque\s+)?(method|function|lemma|predicate|datatype)\b')
        match = pattern.search(line)
        if match:
            qualifier = (match.group(1) or '').strip()
            keyword = match.group(2)
            return f"{qualifier} {keyword}".strip()
    
    return ""

def relevant_dependencies(code_str,funcnames):
    myname = definition_name(code_str)
    return list([f for f in dafny_dependencies(code_str) if f in funcnames and not f==myname])

# Loads a Dafny program and returns a dictionary for the form
# {funcname1:[dependency_list]}
def dependency_graph(filename):
    code = loadrawtxt(filename)
    funclist = partition_dafny_definitions(code)
    funcnames = [definition_name(f) for f in funclist]
    funcdict = {definition_name(f):f for f in funclist}
    return {f:relevant_dependencies(funcdict[f],funcnames) for f in funcnames}

# Loads a Dafny program and returns a dictionary for the form
# {funcname1:[[dependency_list],codetext]}
def atomized_code(filename):
    code = loadrawtxt(filename)
    funclist = partition_dafny_definitions(code)
    funcnames = [definition_name(f) for f in funclist]
    funcdict = {definition_name(f): f for f in funclist}

    return {
        f: [
            relevant_dependencies(funcdict[f], funcnames),  # [0] dependencies
            funcdict[f],                                    # [1] code
            definition_type(funcdict[f])                    # [2] type (e.g. 'opaque function')
        ]
        for f in funcnames
    }

def find_definition_end(dafny_code: str, start_pos: int, max_pos: int) -> int:
    """
    Find the end of a definition starting at start_pos, looking no further than max_pos.
    Returns the position after the closing brace of the definition.
    """
    brace_count = 0
    in_definition = False
    
    for i in range(start_pos, max_pos):
        char = dafny_code[i]
        if char == '{':
            if not in_definition:
                in_definition = True
            brace_count += 1
        elif char == '}':
            brace_count -= 1
            if in_definition and brace_count == 0:
                return i + 1
    
    # If we didn't find a proper end, return max_pos
    return max_pos

def create_skeleton_with_placeholders(dafny_code: str) -> Tuple[str, Dict[str, str]]:
    """
    Creates a skeleton file with placeholders and a mapping of placeholders to atom names.
    The placeholder_mapping maps placeholders to atom names, not the actual bodies.
    Returns: (skeleton_file, placeholder_mapping)
    """
    # Find the actual start positions of each definition in the original file
    definition_pattern = re.compile(r'^[ \t]*(?:ghost\s+|opaque\s+)?(method|function|lemma|predicate|datatype)\b', re.MULTILINE)
    
    # Find all definition start positions and their names
    definition_info = []
    for match in definition_pattern.finditer(dafny_code):
        start_pos = match.start()
        # Extract the definition name from the line
        line_start = dafny_code.rfind('\n', 0, start_pos) + 1
        line_end = dafny_code.find('\n', start_pos)
        if line_end == -1:
            line_end = len(dafny_code)
        line = dafny_code[line_start:line_end]
        # Get the name (robustly, even for similar names)
        name_match = re.search(r'(?:method|function|lemma|predicate|datatype)\s+([a-zA-Z_][a-zA-Z0-9_\']*)', line)
        if name_match:
            name = name_match.group(1)
        else:
            name = f'unknown_{start_pos}'
        definition_info.append((name, start_pos))
    
    # Add a sentinel for the end of the file
    definition_info.append((None, len(dafny_code)))
    
    skeleton_lines = []
    placeholder_mapping = {}
    prev_end = 0
    for i in range(len(definition_info) - 1):
        name, start_pos = definition_info[i]
        next_start = definition_info[i + 1][1]
        # Find the end of this definition
        end_pos = find_definition_end(dafny_code, start_pos, next_start)
        if i == 0:
            # Only add preamble before the first definition
            preamble_content = dafny_code[prev_end:start_pos]
            if preamble_content:
                skeleton_lines.append(preamble_content)
        # Add placeholder
        placeholder = f"//ATOM_PLACEHOLDER_{name}"
        skeleton_lines.append(placeholder)
        # Map placeholder to atom name (not the body)
        placeholder_mapping[placeholder] = name
        prev_end = end_pos
        # Add content between this definition and the next one
        between_content = dafny_code[end_pos:next_start]
        if between_content:
            skeleton_lines.append(between_content)
    # Add any trailing content
    if prev_end < len(dafny_code):
        skeleton_lines.append(dafny_code[prev_end:])
    skeleton = ''.join(skeleton_lines)
    return skeleton, placeholder_mapping

def reconstruct_from_json(json_file_path: str, output_file_path: str = None) -> str:
    """
    Reconstructs the original Dafny file from a JSON file.
    Supports both old format (with "data" key) and new enhanced format (with "skeleton" and "placeholder_mapping" keys).
    Returns the reconstructed content as a string.
    """
    with open(json_file_path, 'r') as f:
        data = json.load(f)
    
    # Check if this is the new enhanced format
    if "skeleton" in data and "placeholder_mapping" in data:
        # New enhanced format
        skeleton = data["skeleton"]
        placeholder_mapping = data["placeholder_mapping"]
        atoms = data.get("atoms", {})
        
        # Sort placeholders by length (longest first) to avoid partial replacements
        sorted_placeholders = sorted(placeholder_mapping.keys(), key=len, reverse=True)
        
        reconstructed = skeleton
        for placeholder in sorted_placeholders:
            atom_name = placeholder_mapping[placeholder]
            # Get the atom body from the atoms section
            if atom_name in atoms and len(atoms[atom_name]) >= 2:
                atom_content = atoms[atom_name][1]  # The actual content is at index 1
                reconstructed = reconstructed.replace(placeholder, atom_content)
            else:
                # Fallback: if atom not found, just remove the placeholder
                reconstructed = reconstructed.replace(placeholder, "")
        
    elif "data" in data:
        # Old format - reconstruct from atoms
        atoms_data = data["data"]
        reconstructed_lines = []
        
        # Sort atoms by name to ensure consistent ordering
        for atom_name in sorted(atoms_data.keys()):
            atom_info = atoms_data[atom_name]
            if len(atom_info) >= 2:
                atom_content = atom_info[1]  # The actual content is at index 1
                reconstructed_lines.append(atom_content)
        
        reconstructed = "\n".join(reconstructed_lines)
        
    else:
        raise ValueError(f"Unsupported JSON format in {json_file_path}. Expected either 'skeleton' and 'placeholder_mapping' keys (enhanced format) or 'data' key (old format).")
    
    # Save to file if output path is provided
    if output_file_path:
        with open(output_file_path, 'w') as f:
            f.write(reconstructed)
        print(f"Reconstructed file saved to: {output_file_path}")
    
    return reconstructed

def atomized_code_with_skeleton(filename):
    """
    Enhanced version that creates both skeleton and atomized structure.
    Returns JSON with skeleton, atoms, and placeholder mapping for exact reconstruction.
    """
    code = loadrawtxt(filename)
    
    # Create skeleton and placeholder mapping
    skeleton, placeholder_mapping = create_skeleton_with_placeholders(code)
    
    # Extract atoms as before
    funclist = partition_dafny_definitions(code)
    funcnames = [definition_name(f) for f in funclist]
    funcdict = {definition_name(f): f for f in funclist}
    
    atoms = {
        f: [
            relevant_dependencies(funcdict[f], funcnames),
            funcdict[f],
            definition_type(funcdict[f])
        ]
        for f in funcnames
    }
    
    return {
        "skeleton": skeleton,
        "atoms": atoms,
        "placeholder_mapping": placeholder_mapping
    }

#print(extract_dafny_function_calls(dafny_method_examle))

def main():
    parser = argparse.ArgumentParser(description='Dafny Atomizer - Decompose and reconstruct Dafny files')
    parser.add_argument('--atomize', metavar='DAFNY_FILE_OR_DIR', help='Atomize a Dafny file or directory into JSON')
    parser.add_argument('--reconstruct', metavar='JSON_FILE_OR_DIR', help='Reconstruct a Dafny file from JSON or directory of JSON files')
    parser.add_argument('--output', '-o', metavar='OUTPUT_FILE', help='Output file path (for reconstruction)')
    parser.add_argument('--recursive', '-r', action='store_true', help='Process directories recursively (when atomizing or reconstructing)')
    parser.add_argument('--skeleton', action='store_true', help='Include skeleton information in JSON output (enhanced format)')
    
    args = parser.parse_args()
    
    if args.atomize and args.reconstruct:
        print("Error: Cannot use both --atomize and --reconstruct at the same time")
        sys.exit(1)
    
    if not args.atomize and not args.reconstruct:
        print("Error: Must specify either --atomize or --reconstruct")
        parser.print_help()
        sys.exit(1)
    
    if args.atomize:
        # Atomize mode
        input_path = args.atomize
        try:
            if os.path.isdir(input_path):
                atomize_directory(input_path, args.recursive, args.skeleton)
            else:
                atomize_dafny_file(input_path, args.skeleton)
        except Exception as e:
            print(f"Error atomizing {input_path}: {e}")
            sys.exit(1)
    
    elif args.reconstruct:
        # Reconstruct mode
        input_path = args.reconstruct
        output_file = args.output
        
        try:
            if os.path.isdir(input_path):
                reconstruct_directory(input_path, args.recursive)
            else:
                # Single file reconstruction
                if not output_file:
                    # Generate output filename from JSON filename
                    if input_path.endswith('.json'):
                        # Preserve any suffix pattern (e.g., _spec.json -> _spec.dfy)
                        base_name = input_path[:-5]  # Remove .json
                        output_file = base_name + '.dfy'
                    else:
                        output_file = input_path + '.dfy'
                
                reconstructed_content = reconstruct_from_json(input_path, output_file)
                print(f"Successfully reconstructed file from {input_path}")
        except Exception as e:
            print(f"Error reconstructing from {input_path}: {e}")
            sys.exit(1)

def atomize_directory(directory_path: str, recursive: bool = False, include_skeleton: bool = False):
    """
    Atomizes all Dafny files in a directory and saves the results to JSON files.
    """
    import glob
    
    # Find all .dfy files in the directory
    if recursive:
        pattern = os.path.join(directory_path, "**/*.dfy")
        dafny_files = glob.glob(pattern, recursive=True)
    else:
        pattern = os.path.join(directory_path, "*.dfy")
        dafny_files = glob.glob(pattern)
    
    if not dafny_files:
        print(f"No .dfy files found in {directory_path}")
        return
    
    print(f"Found {len(dafny_files)} Dafny files to atomize")
    
    successful = 0
    failed = 0
    
    for dafny_file in dafny_files:
        try:
            print(f"Processing: {dafny_file}")
            atomize_dafny_file(dafny_file, include_skeleton)
            successful += 1
        except Exception as e:
            print(f"Failed to process {dafny_file}: {e}")
            failed += 1
    
    print(f"\nDirectory processing complete:")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total: {len(dafny_files)}")

def atomize_dafny_file(dafny_file_path: str, include_skeleton: bool = False):
    """
    Atomizes a Dafny file and saves the results to JSON files.
    """
    # Generate result based on skeleton parameter
    if include_skeleton:
        result = atomized_code_with_skeleton(dafny_file_path)
    else:
        result = {
            "data": atomized_code(dafny_file_path)
        }
    
    # Create output filename with .json extension
    output_filename = os.path.splitext(dafny_file_path)[0] + ".json"
    
    # Save JSON to file
    with open(output_filename, 'w') as f:
        json.dump(result, f, indent=2)
    
    # Also output JSON to stdout
    print(json.dumps(result))
    print(f"\nJSON saved to: {output_filename}")

def reconstruct_directory(directory_path: str, recursive: bool = False):
    """
    Reconstructs all JSON files in a directory back to Dafny files.
    """
    import glob
    
    # Find all .json files in the directory
    if recursive:
        pattern = os.path.join(directory_path, "**/*.json")
        json_files = glob.glob(pattern, recursive=True)
    else:
        pattern = os.path.join(directory_path, "*.json")
        json_files = glob.glob(pattern)
    
    # Filter out files that are already reconstructed
    json_files = [f for f in json_files if not (
        f.endswith('.dfy')
    )]
    
    if not json_files:
        print(f"No .json files found in {directory_path}")
        return
    
    print(f"Found {len(json_files)} JSON files to reconstruct")
    
    successful = 0
    failed = 0
    
    for json_file in json_files:
        try:
            print(f"Processing: {json_file}")
            
            # Generate output filename - preserve suffix pattern
            if json_file.endswith('.json'):
                base_name = json_file[:-5]  # Remove .json
                output_file = base_name + '.dfy'
            else:
                output_file = json_file + '.dfy'
            
            reconstructed_content = reconstruct_from_json(json_file, output_file)
            successful += 1
        except Exception as e:
            print(f"Failed to process {json_file}: {e}")
            failed += 1
    
    print(f"\nDirectory reconstruction complete:")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total: {len(json_files)}")

if __name__ == "__main__":
    main()
