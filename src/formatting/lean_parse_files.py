#!/usr/bin/env python3
"""
Script to check .lean files for proper formatting according to the vericoding template.

Expected format:
1. Import statements (import and open statements)
2. Description section (/-! ... -/)
3. Implementation (text description followed by def with sorry)
4. Specification (text description followed by theorem with sorry)

Each section should be separated by empty lines, and there should be no empty lines within each section.
"""

import os
import sys
import json
import shutil
import argparse
from pathlib import Path
from typing import List, Tuple, Dict, Any
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from convert_from_yaml import spec_to_yaml

section_starters = ["/--", "/-!", "/-", "--", "def", "theorem", 
                    "inductive", "structure", "abbrev", "instance", 
                    "class", "opaque", "axiom", "noncomputable"]

def startswith(line: str, liststr: List[str]) -> bool:
    """
    Check if a line starts with any of the strings in the given list.
    
    Args:
        line: The line to check
        liststr: List of strings to check against
        
    Returns:
        True if the line starts with any string in liststr, False otherwise
    """
    return any(line.startswith(prefix) for prefix in liststr)

def consolidate_partial_results(partial_results, results):
    if not partial_results:
        return results
    
    final_results = []
    while partial_results and partial_results[-1]["type"] in ["commment", "doc", "empty"]:
        final_results.insert(0, {
            "type": partial_results[-1]["type"],
            "string": partial_results[-1]["string"]
        })
        partial_results.pop()
    
    if not partial_results:
        if final_results:
            results.extend(final_results)
        return results
        
    consolidated_string = "\n".join([result["string"] for result in partial_results])

    results.append({
        "type": partial_results[0]["type"],
        "string": consolidated_string
    })

    if final_results:
        results.extend(final_results)

    return results

def parse_lean_file(file_path: str) -> Tuple[str, List[Dict[str, str]]]:
    """
    Parse a Lean file according to the specified rules.
    
    Returns:
        Tuple of (status, results) where status is "ok" or an error message,
        and results is a list of JSON objects or empty dict if error.
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        return f"Error reading file {file_path}: {str(e)}", {}
    
    results = []
    partial_results = []
    imports = ""
    state = "preamble"
    i = 0
    description_found = False
    
    while i < len(lines):
        line = lines[i].rstrip()
        
        # Preamble state
        if state == "preamble":
            if startswith(line, ["import", "open", "set_option"]):
                imports += lines[i]
                i += 1
            elif startswith(line, ["/-!"]):
                # Parse description section
                if description_found:
                    return f"Multiple description sections found in {file_path}", {}
                
                description_found = True
                description_lines = []
                
                # Find the end of the description section
                while i < len(lines) and not lines[i].rstrip().endswith("-/"):
                    description_lines.append(lines[i])
                    i += 1
                
                if i < len(lines):
                    description_lines.append(lines[i])  # Add the closing -/
                    i += 1
                
                description_text = "".join(description_lines)
                results.append({
                    "type": "desc",
                    "string": description_text
                })
                
            elif startswith(line, section_starters) or line.startswith("namespace"):
                # Exit preamble state
                if imports.rstrip():  # Only add if there are imports
                    results.append({
                        "type": "imports",
                        "string": imports.rstrip()
                    })
                state = "main"
            elif line == "":
                # Skip empty lines in preamble
                i += 1
            else:
                return f"Unexpected line in preamble: '{line}' in {file_path}", {}
        
        # Main parsing state
        elif state == "main":
            if startswith(line, ["/--"]):
                # Parse comment section
                comment_lines = []
                
                # Find the end of the comment section
                while i < len(lines) and not lines[i].rstrip().endswith("-/"):
                    comment_lines.append(lines[i])
                    i += 1
                
                if i < len(lines):
                    comment_lines.append(lines[i])  # Add the closing -/
                    i += 1
                
                comment_text = "".join(comment_lines)
                partial_results.append({
                    "type": "doc",
                    "string": comment_text
                })
                
            elif startswith(line, ["--"]):
                # Parse comment section
                comment_lines = []
                
                # Append as long as the line starts with --
                while i < len(lines) and lines[i].rstrip().startswith("--"):
                    comment_lines.append(lines[i])
                    i += 1
                
                comment_text = "".join(comment_lines)
                partial_results.append({    
                    "type": "comment",
                    "string": comment_text
                })
                
            elif startswith(line, ["inductive", "structure", "abbrev", "instance", "class", "opaque", "axiom", "noncomputable"]):
                results = consolidate_partial_results(partial_results, results)
                partial_results = []

                # Parse construction
                constr_lines = []
                first_line = True
                while i < len(lines):
                    current_line = lines[i].rstrip()
                    if (startswith(current_line, section_starters) and not first_line) or not current_line:
                        break
                    constr_lines.append(lines[i])
                    first_line = False
                    i += 1
                
                if constr_lines:
                    constr_text = "".join(constr_lines)
                    partial_results.append({
                        "type": "constr",
                        "string": constr_text
                    })
                
            elif startswith(line, ["def"]):
                results = consolidate_partial_results(partial_results, results)
                partial_results = []

                # Parse definition signature
                sig_lines = []
                ends_with_equality = False
                first_line = True
                # Find the end of the signature (line ending with :=)
                while i < len(lines):
                    current_line = lines[i].rstrip()
                    if current_line.endswith(":="):
                        ends_with_equality = True
                        break
                    elif (startswith(current_line, section_starters) and not first_line):
                        break
                    sig_lines.append(lines[i])
                    first_line = False
                    i += 1
                
                if i < len(lines) and ends_with_equality:
                    sig_lines.append(lines[i])  # Add the line with :=
                    i += 1
                
                sig_text = "".join(sig_lines)
                if ends_with_equality:
                    results.append({
                        "type": "sig",
                        "string": sig_text
                    })
                
                    # Parse implementation      
                    impl_lines = []
                    while i < len(lines):
                        current_line = lines[i].rstrip()
                        if startswith(current_line, section_starters):
                            break
                        impl_lines.append(lines[i])
                        i += 1
                    
                    if impl_lines:
                        impl_text = "".join(impl_lines)
                        results.append({
                            "type": "impl",
                            "string": impl_text
                        })

                else:
                    # check if it ends with ":= sorry" or ":= by sorry"
                    sig_text_no_ws = ''.join(sig_text.split())
                    if sig_text_no_ws.endswith(":=sorry"):
                        # find last position of "sorry"
                        sorry_pos = sig_text.rfind("sorry")
                        results.append({
                            "type": "sig",
                            "string": sig_text[:sorry_pos].rstrip()
                        })
                        results.append({
                            "type": "impl",
                            "string": "sorry"
                        })
                    elif sig_text_no_ws.endswith(":=bysorry"):
                        # find last position of "by"
                        sorry_pos = sig_text.rfind("by")
                        results.append({
                            "type": "sig",
                            "string": sig_text[:sorry_pos].rstrip()
                        })
                        results.append({
                            "type": "impl",
                            "string": "sorry"
                        })
                    else:
                        partial_results.append({
                            "type": "sig",
                            "string": sig_text
                        })
                    
            elif startswith(line, ["theorem"]):
                results = consolidate_partial_results(partial_results, results)
                partial_results = []

                # Parse theorem condition
                cond_lines = []
                ends_with_by = False
                first_line = True

                # Find the end of the condition (line ending with ":= by")
                while i < len(lines):
                    current_line = lines[i].rstrip()
                    if current_line.endswith(":= by"):
                        ends_with_by = True
                        break
                    elif (startswith(current_line, section_starters) and not first_line):
                        break
                    cond_lines.append(lines[i])
                    first_line = False
                    i += 1
                
                if i < len(lines) and ends_with_by:
                    cond_lines.append(lines[i])  # Add the line with ":= by"
                    i += 1
                
                cond_text = "".join(cond_lines)
                if ends_with_by:
                    results.append({
                        "type": "cond",
                        "string": cond_text
                    })

                    # Parse proof
                    proof_lines = []
                    while i < len(lines):
                        current_line = lines[i].rstrip()
                        if startswith(current_line, section_starters):
                            break
                        proof_lines.append(lines[i])
                        i += 1
                
                    if proof_lines:
                        proof_text = "".join(proof_lines)
                        results.append({
                            "type": "proof",
                            "string": proof_text
                        })
                else:
                    # check if it ends with ":= sorry" or ":= by sorry"
                    cond_text_no_ws = ''.join(cond_text.split())
                    if cond_text_no_ws.endswith(":=sorry") or cond_text_no_ws.endswith(":=bysorry"):
                        # find last position of "sorry"
                        sorry_pos = cond_text.rfind("sorry")
                        results.append({
                            "type": "cond",
                            "string": cond_text[:sorry_pos].rstrip()
                        })
                        results.append({
                            "type": "proof",
                            "string": cond_text[sorry_pos:].strip()
                        })
                    else:
                        partial_results.append({
                            "type": "cond",
                            "string": cond_text
                        })

            elif line.startswith("namespace"):
                partial_results.append({
                    "type": "namespace",
                    "string": lines[i]
                })                
                i += 1

            elif line.startswith("end"):
                partial_results.append({
                    "type": "namespace",
                    "string": lines[i]
                })                
                i += 1

            elif line == "":
                partial_results.append({
                    "type": "empty",
                    "string": ""
                })                
                i += 1

            else:
                partial_results.append({
                    "type": "other",
                    "string": lines[i]
                })                
                i += 1

    if partial_results:
        results = consolidate_partial_results(partial_results, results)
        partial_results = []

    return "ok", results

def main():
    """Main function to check all .lean files in the specified directory."""
    parser = argparse.ArgumentParser(
        description="Parse Lean files and check for proper formatting according to the vericoding template."
    )
    parser.add_argument(
        "folder_path", 
        type=str, 
        help="Path to folder containing Lean files to parse"
    )
    parser.add_argument(
        "parsing_results_file", 
        type=str, 
        nargs="?", 
        default=None,
        help="Path to parsing results JSON file (default: parsing_results.json in parent directory)"
    )
    
    args = parser.parse_args()
    
    # Convert to Path objects
    folder_path = Path(args.folder_path)
    if not folder_path.exists():
        print(f"Error: Folder '{folder_path}' does not exist.")
        sys.exit(1)
    
    if not folder_path.is_dir():
        print(f"Error: '{folder_path}' is not a directory.")
        sys.exit(1)
    
    # Set default parsing results file path if not provided
    if args.parsing_results_file is None:
        parsing_results_file = folder_path.parent / f"parsing_results_{folder_path.name}.json"
    else:
        parsing_results_file = Path(args.parsing_results_file)
    
    # Find all .lean files in the specified directory
    lean_files = list(folder_path.glob('*.lean')) 
    if not lean_files:
        print(f"No .lean files found in '{folder_path}'.")
        return
    
    print(f"Checking {len(lean_files)} .lean files in '{folder_path}' for proper formatting...\n")
    
    wrong_format_files = []
    parsing_results_obj = {}
    count_parsing_error = 0
    for file_path in sorted(lean_files):

        status, parsing_results = parse_lean_file(file_path)

        if status != "ok":
            count_parsing_error += 1
            print(f"✗ {file_path.name}: {status}")
            wrong_format_files.append(file_path.name)
        else:
            # append parsing results to parsing_results_list
            parsing_results_obj[file_path.name] = {
                "status": status,
                "results": parsing_results
            }
                        
    print(f"\nSummary:")
    print(f"Total files checked: {len(lean_files)}")
    print(f"Files with parsing error: {count_parsing_error}")
    
    if wrong_format_files:
        print(f"\nFiles with wrong format:")
        for file_name in wrong_format_files:
            print(f"  - {file_name}")
    else:
        print("\nAll files have the correct format!")
    print()
           
    # Save results to JSON file
    with open(parsing_results_file, "w") as f:
        json.dump(parsing_results_obj, f, indent=2)
    
    print(f"Parsing results saved to: {parsing_results_file}")
    

if __name__ == "__main__":
    main()
