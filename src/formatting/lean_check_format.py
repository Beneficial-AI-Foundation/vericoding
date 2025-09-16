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
from pathlib import Path
from typing import List, Tuple, Dict, Any
import sys
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

def two_sorry_types(actual_types, parsing_results):
    
    if len(parsing_results) < 6:
        return False
    if actual_types[-6:] == ['doc', 'sig', 'impl', 'doc', 'cond', 'proof']:
        for i in [-1,-4]:
            if not "sorry" in parsing_results[i]["string"]:
                return False
        for i in [-2,-3,-5,-6]:
            if "sorry" in parsing_results[i]["string"]:
                return False
        for i in range(len(parsing_results)-6):
            if "sorry" in parsing_results[i]["string"]:
                return False
        return True
    return False

def check_file_format(file_path):
    """Check if a .lean file follows the expected format using parse_lean_file."""
    # First run parse_lean_file on the file
    status, parsing_results = parse_lean_file(file_path)
    
    # If an error is raised, return the status
    if status != "ok":
        return (status, {}, {})
     
    # Extract the types from parsing_results
    actual_types = [result["type"] for result in parsing_results]
    for result in parsing_results:
        if result["type"] == "imports":
            result["string"] = remove_empty_lines(result["string"]).rstrip()
        else:
            result["string"] = result["string"].rstrip()

    

    # Check if the actual types match the expected order
    if actual_types == ["desc", "imports", "doc", "sig", "impl", "doc", "cond", "proof"]:
        # expected_order = ["desc", "imports", "doc", "sig", "impl", "doc", "cond", "proof"]
        file_components = {
            "description": parsing_results[0]["string"].rstrip(),  # desc
            "imports": parsing_results[1]["string"].rstrip(),  # imports
            "def_text": parsing_results[2]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[3]["string"].rstrip(),  # sig
            "def_impl": parsing_results[4]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[5]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[6]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[7]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    elif actual_types == ["imports", "doc", "sig", "impl", "doc", "cond", "proof"]:
        # expected_order = ["imports", "doc", "sig", "impl", "doc", "cond", "proof"]
        file_components = {
            "description": "",  # desc
            "imports": parsing_results[0]["string"].rstrip(),  # imports
            "def_text": parsing_results[1]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[2]["string"].rstrip(),  # sig
            "def_impl": parsing_results[3]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[4]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[5]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[6]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    elif actual_types == ["desc", "doc", "sig", "impl", "doc", "cond", "proof"]:
        # expected_order = ["desc", "doc", "sig", "impl", "doc", "cond", "proof"]
        file_components = {
            "description": parsing_results[0]["string"].rstrip(),  # desc
            "imports": "",  # imports
            "def_text": parsing_results[1]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[2]["string"].rstrip(),  # sig
            "def_impl": parsing_results[3]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[4]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[5]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[6]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    elif actual_types == ['desc', 'imports', 'doc', 'constr', 'empty', 'doc', 'sig', 'impl', 'doc', 'cond', 'proof']:
        # expected_order = ["desc", "doc", "sig", "impl", "doc", "cond", "proof"]
        file_components = {
            "description": parsing_results[0]["string"].rstrip(),  # desc
            "imports": parsing_results[1]["string"].rstrip() + "\n\n" + 
                       parsing_results[2]["string"].rstrip() + "\n" +
                       parsing_results[3]["string"].rstrip(),  # imports
            "def_text": parsing_results[5]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[6]["string"].rstrip(),  # sig
            "def_impl": parsing_results[7]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[8]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[9]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[10]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    elif actual_types == ['desc', 'imports', 'doc', 'constr', 'empty', 'doc', 'constr', 'empty', 'doc', 'sig', 'impl', 'doc', 'cond', 'proof']:
        # expected_order = ["desc", "doc", "sig", "impl", "doc", "cond", "proof"]
        file_components = {
            "description": parsing_results[0]["string"].rstrip(),  # desc
            "imports": parsing_results[1]["string"].rstrip() + "\n\n" + 
                       parsing_results[2]["string"].rstrip() + "\n" +
                       parsing_results[3]["string"].rstrip() + "\n" + 
                       parsing_results[4]["string"].rstrip() + "\n" +
                       parsing_results[5]["string"].rstrip() + "\n" +
                       parsing_results[6]["string"].rstrip(),  # imports
            "def_text": parsing_results[8]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[9]["string"].rstrip(),  # sig
            "def_impl": parsing_results[10]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[11]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[12]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[13]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    elif two_sorry_types(actual_types, parsing_results):
        imports_start = 0
        if parsing_results[0]["type"] == "desc":
            description = parsing_results[0]["string"].rstrip()
            imports_start = 1
        else:
            description = ""

        if parsing_results[imports_start]["type"] == "imports":
            imports = parsing_results[imports_start]["string"].rstrip() + "\n\n"
            imports_start += 1
        else:
            imports = ""

        for i in range(imports_start, len(parsing_results)-6):
            imports += parsing_results[i]["string"].rstrip() + "\n"

        file_components = {
            "description": description,
            "imports": imports.rstrip(),  # imports
            "def_text": parsing_results[-6]["string"].rstrip(),  # first doc
            "def_sig": parsing_results[-5]["string"].rstrip(),  # sig
            "def_impl": parsing_results[-4]["string"].rstrip(),  # impl
            "theorem_text": parsing_results[-3]["string"].rstrip(),  # second doc
            "theorem_cond": parsing_results[-2]["string"].rstrip(),  # cond
            "theorem_proof": parsing_results[-1]["string"].rstrip()  # proof
        }
        return ("ok", file_components, parsing_results)

    else:
        return ("Wrong component order", {}, parsing_results)

def remove_empty_lines(text):
    """Remove empty lines from the text."""
    return "\n".join([line for line in text.split('\n') if line.rstrip() != ''])

def process_file_remove_strings(file_path: str, strings_to_remove: List[str], output_path: str = None) -> str:
    """
    Process a file line by line, strip whitespace, and remove occurrences of specified strings.
    
    Args:
        file_path: Path to the input file
        strings_to_remove: List of strings to remove from each line
        output_path: Optional path for output file. If None, overwrites the input file.
        
    Returns:
        The processed content as a string
        
    Raises:
        FileNotFoundError: If the input file doesn't exist
        IOError: If there's an error reading or writing the file
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        raise IOError(f"Error reading file {file_path}: {str(e)}")
    
    processed_lines = []
    for line in lines:
        # Strip whitespace from the line
        stripped_line = line.strip()
        
        # Remove each string from the stripped line
        should_remove = False
        for string_to_remove in strings_to_remove:
            if string_to_remove in stripped_line:
                if stripped_line != string_to_remove:
                    raise ValueError(f"String '{string_to_remove}' found but it is not the whole line")
                else:
                    should_remove = True
                    break

        if not should_remove:
            processed_lines.append(stripped_line)
    
    # Join the processed lines
    processed_content = '\n'.join(processed_lines)
    
    # Write to output file
    target_path = output_path if output_path else file_path
    try:
        with open(target_path, 'w', encoding='utf-8') as f:
            f.write(processed_content)
    except Exception as e:
        raise IOError(f"Error writing to file {target_path}: {str(e)}")
    
    return processed_content

def build_spec_from_result(result):
    """Build a spec dictionary from the parsed result, carefully combining description, def_text and theorem_text into vc-helpers."""
    
    # Build vc-description by combining description, def_text, and theorem_text
    description_parts = []
    
    # Process description section
    description = result["description"]
    if description.startswith("/-!"):
        description = description.replace("/-!", "/- ")
    if description.rstrip():
        for line in description.split('\n'):
            if not line.strip().startswith('\"code\"'):
                description_parts.append(line)
        if description_parts:
            description_parts.append("")
    
    # Process def_text section
    def_text = result["def_text"]
    if def_text.startswith("/--"):
        def_text = def_text.replace("/--", "/- ")
    if def_text.rstrip():
        for line in def_text.split('\n'):
            description_parts.append(line)
        if description_parts:
            description_parts.append("")
    
    # Process theorem_text section
    theorem_text = result["theorem_text"]
    if theorem_text.startswith("/--"):
        theorem_text = theorem_text.replace("/--", "/- ")
    if theorem_text.rstrip():
        for line in theorem_text.split('\n'):
            description_parts.append(line)
    
    # Build the spec dictionary
    spec = {
        "vc-description": "\n".join(description_parts).rstrip(),
        "vc-preamble": result["imports"].rstrip(),
        "vc-helpers": "-- <vc-helpers>\n-- </vc-helpers>",
        "vc-signature": result["def_sig"].rstrip(),
        "vc-implementation": "-- <vc-implementation>\n" + result["def_impl"].rstrip() + "\n-- </vc-implementation>",
        "vc-condition": result["theorem_cond"].rstrip(),
        "vc-proof": "-- <vc-proof>\n" + result["theorem_proof"].rstrip() + "\n-- </vc-proof>",
        "vc-postamble": ""
    }
    
    return spec


def write_yaml_file(result, output_path):
    """Write the JSON result to a YAML file in the specified format using spec_to_yaml."""
    # First part: build the spec object by combining description, def_text and theorem_text
    spec = build_spec_from_result(result)
    
    # Second part: write the spec object to YAML file using spec_to_yaml
    required_keys = [
        'vc-description',
        'vc-preamble', 
        'vc-helpers',
        'vc-signature',
        'vc-implementation',
        'vc-condition',
        'vc-proof',
        'vc-postamble'
    ]
    spec_to_yaml(spec, output_path, required_keys=required_keys)

def main():
    """Main function to check all .lean files in the current directory."""
    lean_dir = Path("benchmarks/lean")
    work_dir = lean_dir / "dafnybench"
    source_dir = work_dir / "poor/unformatted"
    yaml_dir = work_dir / "yaml"
    bad_dir = work_dir / "poor/bad"
    parsing_results_file = work_dir / "poor/parsing_results.json"

    lean_files = list(source_dir.glob('*.lean')) 
    if not lean_files:
        print("No .lean files found in the current directory.")
        return
    
    
    print(f"Removing unnecessary lines...\n")
    strings_to_remove = [
        "namespace DafnyBenchmarks",
        "end DafnyBenchmarks",
        "import Std",
        "open Std.Do"
    ]
    for file_path in sorted(lean_files):
        process_file_remove_strings(file_path, strings_to_remove, file_path)
 

    # # Create directories if they don't exist
    # yaml_dir.mkdir(exist_ok=True)
    # bad_dir.mkdir(exist_ok=True)

    # print(f"Checking {len(lean_files)} .lean files for proper formatting...\n")
    
    # wrong_format_files = []
    # parsing_results_obj = {}
    # count_parsing_error = 0
    # for file_path in sorted(lean_files):
    #     if status != "ok":
    #         count_parsing_error += 1
    #         print(f"✗ {file_path.name}: {status}")
    #         wrong_format_files.append(file_path.name)
            
    #         # Copy the file to numpy_bad directory
    #         bad_file_path = bad_dir / file_path.name
    #         shutil.copy2(file_path, bad_file_path)
    #         print(f"  → Copied to {bad_file_path}")

    #     else:
    #         # append parsing results to parsing_results_list
    #         parsing_results_obj[file_path.name] = {
    #             "status": status,
    #             "results": parsing_results
    #         }
    

    # print(f"\nSummary:")
    # print(f"Total files checked: {len(lean_files)}")
    # # print(f"Files with correct format: {len(lean_files) - len(wrong_format_files)}")
    # # print(f"Files with wrong component order: {count_wrong_component_order}")
    # print(f"Files with parsing error: {count_parsing_error}")
    
    # if wrong_format_files:
    #     print(f"\nFiles with wrong format:")
    #     for file_name in wrong_format_files:
    #         print(f"  - {file_name}")
    # else:
    #     print("\nAll files have the correct format!")
    # print()
           
    # # Save results to JSON file
    # with open(parsing_results_file, "w") as f:
    #     json.dump(parsing_results_obj, f, indent=2)
    

if __name__ == "__main__":
    main()
