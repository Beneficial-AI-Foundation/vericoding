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
from pathlib import Path
from typing import List

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from convert_from_yaml import spec_to_yaml

section_starters = [
    "/--",
    "/-!",
    "/-",
    "--",
    "def",
    "theorem",
    "inductive",
    "structure",
    "abbrev",
    "instance",
    "class",
    "opaque",
    "axiom",
    "noncomputable",
]


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
    if actual_types[-6:] == ["doc", "sig", "impl", "doc", "cond", "proof"]:
        for i in [-1, -4]:
            if "sorry" not in parsing_results[i]["string"]:
                return False
        for i in [-2, -3, -5, -6]:
            if "sorry" in parsing_results[i]["string"]:
                return False
        for i in range(len(parsing_results) - 6):
            if "sorry" in parsing_results[i]["string"]:
                return False
        return True
    return False


def process_comments(comment_list):
    comment_parts = []
    for comment in comment_list:
        if comment.startswith("/-!"):
            comment = comment.replace("/-!", "/- ")
        if comment.startswith("/--"):
            comment = comment.replace("/--", "/- ")
        if comment.rstrip():
            for line in comment.split("\n"):
                comment_parts.append(line)
            if comment_parts:
                comment_parts.append("")
    return "\n".join(comment_parts).rstrip()


def check_file_format(file_path, parsing_results):
    # Extract the types from parsing_results
    parsing_type = get_parsing_type(parsing_results)
    for result in parsing_results:
        if result["type"] == "imports":
            result["string"] = remove_empty_lines(result["string"]).rstrip()
        else:
            result["string"] = result["string"].rstrip()

    # Empty spec
    spec = {
        "vc-description": "",
        "vc-preamble": "",
        "vc-helpers": "",
        "vc-definitions": "",
        "vc-theorems": "",
        "vc-postamble": "",
    }

    if parsing_type.endswith(
        "sig0-impl1-doc0-cond0-proof1"
    ) and parsing_type.startswith("2-"):
        description = []
        preamble = []
        for i in range(len(parsing_results) - 5):
            if parsing_results[i]["type"] in ["desc", "doc", "empty", "comment"]:
                description.append(parsing_results[i]["string"].rstrip())
                continue
            elif parsing_results[i]["type"] in [
                "imports",
                "sig",
                "impl",
                "cond",
                "proof",
                "constr",
            ]:
                preamble.append(parsing_results[i]["string"].rstrip())
                continue
            else:
                raise ValueError(f"Unexpected type: {parsing_results[i]['type']}")
        spec["vc-description"] = process_comments(description)
        spec["vc-preamble"] = "\n".join(preamble)
        spec["vc-definitions"] = (
            parsing_results[-5]["string"].rstrip()
            + "\n"
            + parsing_results[-4]["string"].rstrip()
        )
        spec["vc-theorems"] = (
            parsing_results[-2]["string"].rstrip()
            + "\n"
            + parsing_results[-1]["string"].rstrip()
        )
        return ("ok", spec)

    else:
        description = []
        preamble = []
        prev_sig = ""
        prev_cond = ""
        prev_sorry_type = 0
        definitions = []
        theorems = []
        postamble = []
        sorry_type = get_sorry_type(parsing_results)[1]
        for result, sorry_type in zip(parsing_results, sorry_type):
            if prev_sig != "":
                if result["type"] == "impl":
                    if sorry_type == 0:
                        preamble.append(prev_sig + "\n" + result["string"].rstrip())
                        preamble.append("")
                        prev_sig = ""
                        continue
                    elif sorry_type == 1:
                        definitions.append(prev_sig + "\n" + result["string"].rstrip())
                        definitions.append("")
                        prev_sig = ""
                        continue
                    else:
                        raise ValueError(
                            f"Unexpected prev_sig and result type {result['type']} with sorry type {sorry_type}"
                        )
                else:
                    if prev_sorry_type == 0:
                        preamble.append(prev_sig)
                        preamble.append("")
                        prev_sig = ""
                    elif prev_sorry_type == 1:
                        definitions.append(prev_sig)
                        definitions.append("")
                        prev_sig = ""
                    else:
                        raise ValueError(
                            f"Unexpected prev_sig with prev_sorry_type {prev_sorry_type}"
                        )
            if prev_cond != "":
                if result["type"] == "proof":
                    if sorry_type == 0:
                        preamble.append(prev_cond + "\n" + result["string"].rstrip())
                        preamble.append("")
                        prev_cond = ""
                        continue
                    elif sorry_type == 1:
                        theorems.append(prev_cond + "\n" + result["string"].rstrip())
                        theorems.append("")
                        prev_cond = ""
                        continue
                    else:
                        raise ValueError(
                            f"Unexpected prev_cond and result type {result['type']} with sorry type {sorry_type}"
                        )
                else:
                    if prev_sorry_type == 0:
                        preamble.append(prev_cond)
                        preamble.append("")
                        prev_cond = ""
                    elif prev_sorry_type == 1:
                        theorems.append(prev_cond)
                        theorems.append("")
                        prev_cond = ""
                    else:
                        raise ValueError(
                            f"Unexpected prev_cond with prev sorry type {prev_sorry_type}"
                        )
            if result["type"] == "cond":
                prev_cond = result["string"].rstrip()
                prev_sorry_type = sorry_type
                continue
            if result["type"] == "sig":
                prev_sig = result["string"].rstrip()
                prev_sorry_type = sorry_type
                continue
            if result["type"] in ["impl", "proof"]:
                raise ValueError(
                    f"Unexpected result type {result['type']} without prev_sig or prev_cond"
                )
            if result["type"] in ["constr", "imports"]:
                preamble.append(result["string"].rstrip())
                preamble.append("")
                continue
            if result["type"] in ["other", "comment"]:
                if "info" in result["string"]:
                    postamble.append(result["string"].rstrip())
                    postamble.append("")
                    continue
                else:
                    description.append(result["string"].rstrip())
                    description.append("")
                    continue
            if result["type"] in ["desc", "doc", "empty", "comment"]:
                if sorry_type == 0:
                    description.append(result["string"].rstrip())
                    description.append("")
                    continue
                else:
                    raise ValueError(
                        f"Unexpected result type {result['type']} with sorry type {sorry_type} and string{result['string']}"
                    )

            raise ValueError(f"Unexpected type: {result['type']}")

        spec["vc-description"] = process_comments(description)
        spec["vc-preamble"] = "\n".join(preamble)
        spec["vc-definitions"] = "\n".join(definitions)
        spec["vc-theorems"] = "\n".join(theorems)
        spec["vc-postamble"] = "\n".join(postamble)
        return ("ok", spec)


def remove_empty_lines(text):
    """Remove empty lines from the text."""
    return "\n".join([line for line in text.split("\n") if line.rstrip() != ""])


def write_yaml_file(spec, output_path):
    """Write the JSON result to a YAML file in the specified format using spec_to_yaml."""

    # Second part: write the spec object to YAML file using spec_to_yaml
    recommended_keys = [
        "vc-description",
        "vc-preamble",
        "vc-helpers",
        "vc-definitions",
        "vc-theorems",
        "vc-postamble",
    ]
    spec_to_yaml(spec, output_path, recommended_keys=recommended_keys)


def get_sorry_type(parsing_results):
    sorry_type = []
    sorry_count = 0
    for result in parsing_results:
        sorry_count += result["string"].count("sorry")
        if "sorry" in result["string"]:
            if result["string"].strip() == "sorry":
                sorry_type.append(1)
            elif result["string"].count("sorry") == 1:
                sorry_type.append(2)
            else:
                sorry_type.append(3)
        else:
            sorry_type.append(0)
    return (sorry_count, sorry_type)


def get_parsing_type(parsing_results):
    sorry_count, sorry_type = get_sorry_type(parsing_results)
    sorry_tags = [
        f"{result['type']}{sorry_ind}"
        for (result, sorry_ind) in zip(parsing_results, sorry_type)
    ]
    return f"{sorry_count}-{'-'.join(sorry_tags)}"


def split_sorries(parsing_results):
    new_parsing_results = []
    for result in parsing_results:
        if result["type"] == "cond" and result["string"].rstrip().endswith("sorry"):
            sorry_split = result["string"].split("sorry")
            new_parsing_results.append({"type": "cond", "string": sorry_split[0]})
            new_parsing_results.append({"type": "proof", "string": "sorry"})
        elif result["type"] == "sig" and result["string"].rstrip().endswith("sorry"):
            sorry_split = result["string"].split("sorry")
            new_parsing_results.append({"type": "sig", "string": sorry_split[0]})
            new_parsing_results.append({"type": "impl", "string": "sorry"})
        else:
            new_parsing_results.append(result)

    return new_parsing_results


def main():
    """Main function to check all .lean files in the current directory."""
    lean_dir = Path("benchmarks/lean")
    work_dir = lean_dir / "fvapps_bad"
    source_name = "files"
    source_dir = work_dir / source_name
    yaml_dir = work_dir / "yaml"
    parsing_results_file = work_dir / f"parsing_results_{source_name}.json"

    lean_files = list(source_dir.glob("*.lean"))
    if not lean_files:
        print("No .lean files found in the current directory.")
        return

    # Create directories if they don't exist
    yaml_dir.mkdir(exist_ok=True)
    # bad_dir.mkdir(exist_ok=True)

    # read parsing results
    with open(parsing_results_file, "r") as f:
        parsing_results_obj = json.load(f)

    parsing_types = {}
    wrong_format_files = []
    for file_path in sorted(lean_files):
        # for file_path in [source_dir / 'fvapps_000003.lean']:
        if file_path.name in parsing_results_obj:
            status = parsing_results_obj[file_path.name]["status"]
            parsing_results = parsing_results_obj[file_path.name]["results"]
            parsing_results = split_sorries(parsing_results)
            if status == "ok":
                try:
                    status, spec = check_file_format(file_path, parsing_results)
                except ValueError as e:
                    print(f"✗ {file_path.name}: {e}")
                    continue
                if status == "ok":
                    write_yaml_file(spec, yaml_dir / (file_path.stem + ".yaml"))
                else:
                    if get_parsing_type(parsing_results) not in parsing_types:
                        parsing_types[get_parsing_type(parsing_results)] = [
                            file_path.name
                        ]
                    else:
                        parsing_types[get_parsing_type(parsing_results)].append(
                            file_path.name
                        )

            else:
                print(f"✗ {file_path.name}: {status}")
                wrong_format_files.append(file_path.name)

    # sort parsing types by count
    parsing_types = sorted(parsing_types.items(), key=lambda x: len(x[1]), reverse=True)
    # print total number of unformatted files
    print(
        f"Total number of unformatted files: {sum([len(x[1]) for x in parsing_types])}"
    )
    # print total number of parsing types
    print(f"Total number of parsing types: {len(parsing_types)}")
    # print top 5 parsing types
    print("Top 10 remaining parsing types")
    for parsing_type, files in parsing_types[:10]:
        print(f"  - {parsing_type}: {len(files)}")
        for file in files:
            print(f"    = {file}")

    # print wrong format files
    print(f"Wrong format files: {wrong_format_files}")

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
