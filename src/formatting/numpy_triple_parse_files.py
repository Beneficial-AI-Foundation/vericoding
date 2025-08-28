#!/usr/bin/env python3
import os
import json
import re
from typing import List, Tuple, Dict, Any

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
    imports = ""
    state = "preamble"
    i = 0
    description_found = False
    
    while i < len(lines):
        line = lines[i].strip()
        
        # Preamble state
        if state == "preamble":
            if line.startswith("import") or line.startswith("open") or line.startswith("set_option"):
                imports += lines[i]
                i += 1
            elif line.startswith("/-!"):
                # Parse description section
                if description_found:
                    return f"Multiple description sections found in {file_path}", {}
                
                description_found = True
                description_lines = []
                
                # Find the end of the description section
                while i < len(lines) and not lines[i].strip().endswith("-/"):
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
                
            elif line.startswith("/--") or line.startswith("--"):
                # Exit preamble state
                if imports.strip():  # Only add if there are imports
                    results.append({
                        "type": "imports",
                        "string": imports.strip()
                    })
                state = "main"
            elif line == "":
                # Skip empty lines in preamble
                i += 1
            else:
                return f"Unexpected line in preamble: '{line}' in {file_path}", {}
        
        # Main parsing state
        elif state == "main":
            if line.startswith("/--"):
                # Parse comment section
                comment_lines = []
                
                # Find the end of the comment section
                while i < len(lines) and not lines[i].strip().endswith("-/"):
                    comment_lines.append(lines[i])
                    i += 1
                
                if i < len(lines):
                    comment_lines.append(lines[i])  # Add the closing -/
                    i += 1
                
                comment_text = "".join(comment_lines)
                results.append({
                    "type": "doc",
                    "string": comment_text
                })
                
            elif line.startswith("--"):
                # Parse comment section
                comment_lines = []
                
                # Append as long as the line starts with --
                while i < len(lines) and lines[i].strip().startswith("--"):
                    comment_lines.append(lines[i])
                    i += 1
                
                comment_text = "".join(comment_lines)
                results.append({
                    "type": "comment",
                    "string": comment_text
                })
                
            elif line.startswith("inductive") or line.startswith("structure") or \
                    line.startswith("abbrev") or line.startswith("instance") or \
                    line.startswith("class") or line.startswith("opaque") or \
                    line.startswith("axiom") or line.startswith("noncomputable"):
                # Parse construction
                constr_lines = []
                while i < len(lines):
                    current_line = lines[i].strip()
                    if not current_line:
                        break
                    constr_lines.append(lines[i])
                    i += 1
                
                if constr_lines:
                    constr_text = "".join(constr_lines)
                    results.append({
                        "type": "constr",
                        "string": constr_text
                    })
                
            elif line.startswith("def"):
                # Parse definition signature
                sig_lines = []
                
                # Find the end of the signature (line ending with :=)
                while i < len(lines) and not lines[i].strip().endswith(":="):
                    sig_lines.append(lines[i])
                    i += 1
                
                if i < len(lines):
                    sig_lines.append(lines[i])  # Add the line with :=
                    i += 1
                
                sig_text = "".join(sig_lines)
                results.append({
                    "type": "sig",
                    "string": sig_text
                })
                
                # Parse implementation
                impl_lines = []
                while i < len(lines):
                    current_line = lines[i].strip()
                    if (current_line.startswith("/--") or 
                        current_line.startswith("--") or 
                        current_line.startswith("def") or 
                        current_line.startswith("theorem")):
                        break
                    impl_lines.append(lines[i])
                    i += 1
                
                if impl_lines:
                    impl_text = "".join(impl_lines)
                    results.append({
                        "type": "impl",
                        "string": impl_text
                    })
                
            elif line.startswith("theorem"):
                # Parse theorem condition
                cond_lines = []
                
                # Find the end of the condition (line ending with ":= by")
                while i < len(lines) and not lines[i].strip().endswith(":= by"):
                    cond_lines.append(lines[i])
                    i += 1
                
                if i < len(lines):
                    cond_lines.append(lines[i])  # Add the line with ":= by"
                    i += 1
                
                cond_text = "".join(cond_lines)
                results.append({
                    "type": "cond",
                    "string": cond_text
                })
                
                # Parse proof
                proof_lines = []
                while i < len(lines):
                    current_line = lines[i].strip()
                    if (current_line.startswith("/--") or 
                        current_line.startswith("--") or 
                        current_line.startswith("def") or 
                        current_line.startswith("theorem")):
                        break
                    proof_lines.append(lines[i])
                    i += 1
                
                if proof_lines:
                    proof_text = "".join(proof_lines)
                    results.append({
                        "type": "proof",
                        "string": proof_text
                    })
                
            elif line == "":
                # Skip empty lines
                i += 1
            else:
                return f"Unexpected line in main state: '{line}' in {file_path}", {}
    
    return "ok", results

def parse_all_files(directory_path: str) -> Dict[str, Any]:
    """
    Parse all .lean files in the specified directory.
    
    Returns:
        Dictionary with file paths as keys and parsing results as values.
    """
    results = {}
    
    for filename in os.listdir(directory_path):
        if filename.endswith('.lean'):
            file_path = os.path.join(directory_path, filename)
            status, parsed_results = parse_lean_file(file_path)
            results[filename] = {
                "status": status,
                "results": parsed_results
            }
    
    return results

if __name__ == "__main__":
    # Parse all files in the numpy_bad directory
    numpy_bad_dir = "benchmarks/lean/numpy_bad"
    parsing_results_file = "benchmarks/lean/parsing_results.json"
    
    if not os.path.exists(numpy_bad_dir):
        print(f"Directory {numpy_bad_dir} not found!")
        exit(1)
    
    all_results = parse_all_files(numpy_bad_dir)
    
    # Print results
    for filename, result in all_results.items():
        # print(f"\n=== {filename} ===")
        # print(f"Status: {result['status']}")
        # if result['status'] == "ok":
            # print(f"Number of parsed sections: {len(result['results'])}")
            # for i, section in enumerate(result['results']):
            #     print(f"  {i+1}. Type: {section['type']}")
            #     print(f"     Length: {len(section['string'])} characters")
        # else:
        if result['status'] != "ok":
            print(f"\n=== {filename} ===")
            print(f"Status: {result['status']}")
            print(f"Error: {result['status']}")
    
    # Save results to JSON file
    with open(parsing_results_file, "w") as f:
        json.dump(all_results, f, indent=2)
    
    print(f"\nResults saved to {parsing_results_file}")
    
    # Summary statistics
    ok_count = 0
    error_count = 0
    error_files = []
    
    for filename, result in all_results.items():
        if result['status'] == 'ok':
            ok_count += 1
        else:
            error_count += 1
            error_files.append((filename, result['status']))
    
    print(f"\n=== PARSING SUMMARY ===")
    print(f"Total files processed: {len(all_results)}")
    print(f"Successful (ok): {ok_count}")
    print(f"Errors: {error_count}")
    print(f"Success rate: {ok_count/len(all_results)*100:.1f}%")
    
    # if error_files:
    #     print(f"\nError files (first 10):")
    #     for filename, error in error_files[:10]:
    #         print(f"  {filename}: {error}")
        
    #     if len(error_files) > 10:
    #         print(f"  ... and {len(error_files) - 10} more error files")
