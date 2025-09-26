#!/usr/bin/env python3
"""
Script to analyze sorry usage patterns in Lean parsing results.

For each key "XXX.lean" in parsing_results.json, this script:
1. Counts the number of 'sorry' in all "strings" fields
2. If there are more than 2 total sorry, prints a warning
3. Otherwise, checks if there is exactly 1 sorry in "impl" and 1 sorry in "proof"
4. If the check fails, prints a warning
5. Copies files with warnings from numpy_all/ to numpy_fix/
"""

import json
import sys
import os
import shutil
from numpy_triple_check_format import write_yaml_file
from numpy_triple_check_format import remove_empty_lines


def analyze_sorry_usage(json_file_path, copy_warning_files=False):
    """Analyze sorry usage patterns in the parsing results."""

    # Read the JSON file
    try:
        with open(json_file_path, "r") as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"Error: File {json_file_path} not found")
        return
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {json_file_path}: {e}")
        return

    warnings = []
    warning_files = []  # Track files with warnings for copying
    error_files = []
    total_lean_files = 0
    count_formatted_files = 0

    for filename, file_data in data.items():
        if not filename.endswith(".lean"):
            continue

        total_lean_files += 1

        if file_data.get("status") != "ok":
            error_files.append(filename)
            continue

        results = file_data.get("results", [])
        total_sorry_count = 0
        impl_sorry_count = 0
        proof_sorry_count = 0

        for result in results:
            if "string" in result:
                string_content = result["string"]
                sorry_count = string_content.count("sorry")
                total_sorry_count += sorry_count

                if result.get("type") == "impl":
                    result["type"] = "impl-sorry"
                    impl_sorry_count += sorry_count
                elif result.get("type") == "proof":
                    result["type"] = "proof-sorry"
                    proof_sorry_count += sorry_count

        # Check if there are more than 2 total sorry
        if total_sorry_count > 2:
            warnings.append(
                f"WARNING: {filename} has {total_sorry_count} total sorry statements"
            )
            warning_files.append(filename)
        # Check if there is exactly 1 sorry in impl and 1 sorry in proof
        elif not (impl_sorry_count == 1 and proof_sorry_count == 1):
            warnings.append(
                f"WARNING: {filename} has {impl_sorry_count} sorry in impl and {proof_sorry_count} sorry in proof (expected 1 each)"
            )
            warning_files.append(filename)
        else:
            count_formatted_files += 1
            status = analyze_code_blocks(results, filename[:-5] + ".yaml")
            if status == "Cannot find sig-impl-sorry":
                warnings.append(f"WARNING: {filename} does not have a sig-impl-sorry")
                warning_files.append(filename)
            elif status == "Cannot find cond-proof-sorry":
                warnings.append(f"WARNING: {filename} does not have a cond-proof-sorry")
                warning_files.append(filename)

    # Print all warnings
    if warnings:
        print("Sorry usage warnings:")
        for warning in warnings:
            print(warning)
        print(f"\nTotal number of warnings: {len(warnings)}")

        # Copy files with warnings if requested
        if copy_warning_files and warning_files:
            copy_warning_files_to_fix_folder(warning_files)
    else:
        print("No warnings found - all files have the expected sorry usage patterns.")
        print("Total number of warnings: 0")

    print()
    # Print error count
    print(f"Total Lean files: {total_lean_files}")
    print(f"Total number of formatted files: {count_formatted_files}")
    print(f"Total number of warnings: {len(warnings)}")
    print(f"Files with errors: {len(error_files)}")
    if error_files:
        print("Files with errors:")
        for error_file in error_files:
            print(f"  - {error_file}")


def copy_warning_files_to_fix_folder(warning_files):
    """Copy files with warnings from numpy_all/ to numpy_fix/ folder."""
    source_dir = "benchmarks/lean/numpy_all"
    dest_dir = "benchmarks/lean/numpy_fix"

    # Create destination directory if it doesn't exist
    os.makedirs(dest_dir, exist_ok=True)

    copied_count = 0
    for filename in warning_files:
        source_path = os.path.join(source_dir, filename)
        dest_path = os.path.join(dest_dir, filename)

        if os.path.exists(source_path):
            try:
                shutil.copy2(source_path, dest_path)
                print(f"Copied: {filename}")
                copied_count += 1
            except Exception as e:
                print(f"Error copying {filename}: {e}")
        else:
            print(f"Warning: Source file {filename} not found in {source_dir}")

    print(f"\nCopied {copied_count} files with warnings to {dest_dir}/")


def analyze_code_blocks(results, filename):
    """
    Analyze code blocks in the parsing results.
    1. Traverse the results for the key "XXX.lean" backwards and makes changes to the keys as it goes along
    2. Finds a key "sig" that appears before an "impl" and relabels it as "sig-impl"
    3. Finds a key "doc" that appears before a "sig-impl" and relabels it as "doc-sig-impl"
    """

    prev_type = None
    count_sig_impl_sorry = 0
    count_cond_proof_sorry = 0
    # print(results)
    # traverse the results in reverse order
    for i in range(len(results) - 1, -1, -1):
        result = results[i]
        if result.get("type") == "impl-sorry":
            prev_type = "impl-sorry"
            continue
        if prev_type == "impl-sorry" and result.get("type") == "sig":
            result["type"] = "sig-impl-sorry"
            prev_type = "sig-impl-sorry"
            count_sig_impl_sorry += 1
            continue
        if prev_type == "sig-impl-sorry" and result.get("type") == "doc":
            result["type"] = "doc-sig-impl-sorry"
            prev_type = "doc-sig-impl-sorry"
            continue
        if result.get("type") == "proof-sorry":
            prev_type = "proof-sorry"
            continue
        if prev_type == "proof-sorry" and result.get("type") == "cond":
            result["type"] = "cond-proof-sorry"
            prev_type = "cond-proof-sorry"
            count_cond_proof_sorry += 1
            continue
        if prev_type == "cond-proof-sorry" and result.get("type") == "doc":
            result["type"] = "doc-cond-proof-sorry"
            prev_type = "doc-cond-proof-sorry"
            continue
        prev_type = result.get("type")

    if count_sig_impl_sorry == 0:
        return "Cannot find sig-impl-sorry"
    if count_cond_proof_sorry == 0:
        return "Cannot find cond-proof-sorry"

    imports_section = ""
    desc_section = ""
    def_text_section = ""
    theorem_text_section = ""
    sig_section = ""
    impl_section = ""
    cond_section = ""
    proof_section = ""

    for result in results:
        if result.get("type") == "imports":
            if imports_section and imports_section[-1] != "\n":
                imports_section += "\n\n"
            elif imports_section:
                imports_section += "\n"
            imports_section += remove_empty_lines(result.get("string"))
        elif result.get("type") == "description":
            if desc_section and desc_section[-1] != "\n":
                desc_section += "\n\n"
            elif desc_section:
                desc_section += "\n"
            desc_section += result.get("string")
        elif result.get("type") == "impl-sorry":
            if impl_section and impl_section[-1] != "\n":
                impl_section += "\n\n"
            elif impl_section:
                impl_section += "\n"
            impl_section += result.get("string")
        elif result.get("type") == "sig-impl-sorry":
            if sig_section and sig_section[-1] != "\n":
                sig_section += "\n\n"
            elif sig_section:
                sig_section += "\n"
            sig_section += result.get("string")
        elif result.get("type") == "doc-sig-impl-sorry":
            result_string = result.get("string")
            if result_string.strip().startswith("/--"):
                result_string = result_string.replace("/--", "/- ")
            if def_text_section and def_text_section[-1] != "\n":
                def_text_section += "\n\n"
            elif def_text_section:
                def_text_section += "\n"
            def_text_section += result_string
        elif result.get("type") == "proof-sorry":
            if proof_section and proof_section[-1] != "\n":
                proof_section += "\n\n"
            elif proof_section:
                proof_section += "\n"
            proof_section += result.get("string")
        elif result.get("type") == "cond-proof-sorry":
            if cond_section and cond_section[-1] != "\n":
                cond_section += "\n\n"
            elif cond_section:
                cond_section += "\n"
            cond_section += result.get("string")
        elif result.get("type") == "doc-cond-proof-sorry":
            result_string = result.get("string")
            if result_string.strip().startswith("/--"):
                result_string = result_string.replace("/--", "/- ")
            if theorem_text_section and theorem_text_section[-1] != "\n":
                theorem_text_section += "\n\n"
            elif theorem_text_section:
                theorem_text_section += "\n"
            theorem_text_section += result_string
        elif result.get("type") in [
            "impl",
            "sig",
            "cond",
            "proof",
            "doc",
            "comment",
            "constr",
        ]:
            result_string = result.get("string")
            if result_string.strip().startswith("/--"):
                result_string = result_string.replace("/--", "/- ")
            if imports_section:
                if imports_section[-1] != "\n":
                    imports_section += "\n\n"
                else:
                    imports_section += "\n"
            imports_section += result_string

    file_object = {
        "imports": imports_section.rstrip(),
        "description": desc_section.rstrip(),
        "def_text": def_text_section.rstrip(),
        "theorem_text": theorem_text_section.rstrip(),
        "def_sig": sig_section.rstrip(),
        "def_impl": impl_section.rstrip(),
        "theorem_cond": cond_section.rstrip(),
        "theorem_proof": proof_section.rstrip(),
    }
    write_yaml_file(file_object, "benchmarks/lean/numpy_yaml/" + filename)
    print(f"Wrote to {filename}")
    return "No errors found"


if __name__ == "__main__":
    json_file = "benchmarks/lean/parsing_results.json"
    copy_warning_files = True

    if len(sys.argv) > 1:
        json_file = sys.argv[1]

    analyze_sorry_usage(json_file, copy_warning_files)
