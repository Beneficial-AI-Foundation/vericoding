#!/usr/bin/env python3

import argparse
import json
import shutil
from pathlib import Path
from ruamel.yaml import YAML, YAMLError
from typing import Dict, Any
from natsort import natsorted

not_novel = [
    ("dafny", "dafnybench"),
    ("dafny", "humaneval"),
    ("verus", "verified_cogen"),
    ("lean", "verina"),
    ("lean", "fvapps"),
    ("lean", "clever"),
]

sources_ref = {
    "dafnybench": "D",
    "humaneval": "H",
    "verified_cogen": "J",
    "verina": "V",
    "fvapps": "F",
    "clever": "C",
    "numpy_simple": "S",
    "numpy_triple": "T",
    "apps": "A",
    "bignum": "B",
}

languages_ref = {"lean": "L", "dafny": "D", "verus": "V"}

source_meta_filename = "tasks_metadata.jsonl"
source_meta_default_path = Path("benchmarks") / source_meta_filename


def get_vericoding_id(
    source: str, language: str, task: str, source_meta: Dict[str, Any]
) -> str:
    """Get the Vericoding ID for a given source, language, and task."""

    return f"{languages_ref[language]}{sources_ref[source]}{source_meta[task]['id']}"


def _sanitize_lean_description(text: str) -> str:
    """Sanitize description text before embedding in a Lean block comment.

    - Replace "+/-" with the single character "±" to avoid accidental
      opening of nested block comments ("/-") inside a "/* */"-style doc.
    - Leave structural "-/" endings and leading "/-" markers intact.
    """
    if not isinstance(text, str) or not text:
        return text
    # Only a minimal, targeted replacement to avoid touching markup.
    return text.replace("+/-", "±")


def spec_to_string(spec: dict, template: list[str]) -> str:
    """Convert YAML spec dict to string by concatenating sections."""
    parts = []

    # Add sections in order, following the reconstruction logic
    for section, start_pad, end_pad in template:
        if section == "\n":  # empty line
            if start_pad:
                raise ValueError("start_pad is not None for empty line")
            if end_pad:
                raise ValueError("end_pad is not None for empty line")
            # if tail of parts is non-empty, add an empty line
            if parts and parts[-1].strip():
                parts.append("")
        elif section in spec:
            if start_pad:
                parts.append(start_pad)
            if spec[section].rstrip():  # non-empty line
                parts.append(spec[section].rstrip())
            if end_pad:
                parts.append(end_pad)
        else:  # section not in spec
            print(f"Warning: Section {section} not found in spec")

    # Join with newlines
    return "\n".join(parts)


def get_template(suffix: str, add_postamble: bool = False) -> list[str]:
    """Get template for the output file."""
    if suffix == "lean":
        template = [
            ("vc-preamble", "-- <vc-preamble>", "-- </vc-preamble>"),
            ("\n", None, None),
            ("vc-helpers", "-- <vc-helpers>", "-- </vc-helpers>"),
            ("\n", None, None),
            ("vc-definitions", "-- <vc-definitions>", "-- </vc-definitions>"),
            ("\n", None, None),
            ("vc-theorems", "-- <vc-theorems>", "-- </vc-theorems>"),
        ]
        if add_postamble:
            template.extend([("\n", None, None), ("vc-postamble", None, None)])
        return template
    elif suffix == "dfy" or suffix == "rs":
        template = [
            ("vc-preamble", "// <vc-preamble>", "// </vc-preamble>"),
            ("\n", None, None),
            ("vc-helpers", "// <vc-helpers>", "// </vc-helpers>"),
            ("\n", None, None),
            ("vc-spec", "// <vc-spec>", "// </vc-spec>"),
            ("vc-code", "// <vc-code>", "// </vc-code>"),
            ("\n", None, None),
            ("vc-postamble", None, None),
        ]
        return template
    else:
        raise ValueError(f"Unsupported suffix: {suffix}")


def convert_spec_to_file(
    spec: dict, output_path: Path, add_postamble: bool = False
) -> None:
    """Convert spec dictionary to target file format by concatenating sections.

    Args:
        spec: Dictionary containing the spec data
        output_path: Path to the output file
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    template = get_template(output_path.suffix[1:], add_postamble)

    # Defensive sanitization for Lean descriptions to avoid unterminated comments
    if output_path.suffix == ".lean" and "vc-description" in spec:
        spec = dict(spec)  # shallow copy to avoid mutating caller's dict
        spec["vc-description"] = _sanitize_lean_description(spec["vc-description"])

    content = spec_to_string(spec, template)

    with open(output_path, "w") as f:
        f.write(content)

    # print(f"Converted spec -> {output_path}")


def convert_yaml_to_file(
    yaml_path: Path, output_path: Path, add_postamble: bool = False
) -> None:
    """Convert YAML spec to target file format by concatenating sections.

    Args:
        yaml_path: Path to the input YAML file
        output_path: Path to the output file
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting
    spec = yaml.load(yaml_path)

    convert_spec_to_file(spec, output_path, add_postamble)
    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_json(yaml_path: Path, output_path: Path) -> None:
    """Convert YAML spec to a JSON file."""

    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting
    spec = yaml.load(yaml_path)

    with open(output_path, "w") as f:
        json.dump(spec, f, ensure_ascii=False, indent=2)

    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_jsonl(
    yaml_path: Path,
    source: str = None,
    language: str = None,
    source_meta_path: Path = None,
    jsonl_path: Path = None,
) -> None:
    """Convert all YAML files in a directory to a single JSONL file."""

    if source is None:
        source = yaml_path.parent.name

    if language is None:
        language = yaml_path.parent.parent.name

    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")

    if source_meta_path is None:
        source_meta_path = source_meta_default_path

    if not source_meta_path.is_file():
        raise ValueError(f"{source_meta_path} is not a file")

    # load jsonl file as a list of dictionaries
    with open(source_meta_path, "r") as f:
        source_meta = {}
        for line in f:
            lineobj = json.loads(line)
            source_meta[lineobj["source_id"]] = lineobj

    # Find all .yaml files in the directory (recursively)
    yaml_files = list(yaml_path.glob("**/*.yaml"))
    yaml_files_id = [
        {
            "id": get_vericoding_id(source, language, yaml_file.stem, source_meta),
            "path": yaml_file,
        }
        for yaml_file in yaml_files
    ]
    yaml_files_id = natsorted(yaml_files_id, key=lambda x: x["id"])

    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return

    # Create output path in parent directory with .jsonl suffix
    output_path = yaml_path.parent / f"{language}_{source}.jsonl"

    processed_count = 0
    skipped_count = 0

    with open(output_path, "w") as f:
        yaml_parser = YAML()
        yaml_parser.preserve_quotes = True  # Preserve original formatting
        for yaml_file_id in yaml_files_id:
            id = yaml_file_id["id"]
            yaml_file = yaml_file_id["path"]
            try:
                # Load the YAML spec
                spec = yaml_parser.load(yaml_file)

                # Validate that spec is a dictionary
                if not isinstance(spec, dict):
                    print(
                        f"Warning: {yaml_file} does not contain a YAML dictionary, skipping"
                    )
                    skipped_count += 1
                    continue

                # Create a new dictionary with id field first
                new_spec = {
                    "id": id,
                    "language": language,
                    "source": source,
                    "source_id": yaml_file.stem,
                }
                new_spec.update(spec)

                # Write as JSON line
                json.dump(new_spec, f, ensure_ascii=False)
                f.write("\n")
                processed_count += 1

            except YAMLError as e:
                print(
                    f"Warning: Failed to parse {yaml_file} as YAML (likely contains raw code instead of YAML): {e}"
                )
                skipped_count += 1
                continue

    print(f"Converted {processed_count} YAML files to {output_path}")
    if skipped_count > 0:
        print(f"Skipped {skipped_count} files that were not valid YAML")


def convert_poor_to_jsonl(
    poor_path: Path,
    source: str = None,
    language: str = None,
    source_meta_path: Path = None,
    jsonl_path: Path = None,
) -> None:
    """Convert all POOR files in a directory to a single JSONL file."""

    if source is None:
        source = poor_path.parent.name

    if language is None:
        language = poor_path.parent.parent.name

    if not poor_path.is_dir():
        raise ValueError(f"{poor_path} is not a directory")

    if source_meta_path is None:
        source_meta_path = source_meta_default_path

    if not source_meta_path.is_file():
        raise ValueError(f"{source_meta_path} is not a file")

    with open(source_meta_path, "r") as f:
        source_meta = {}
        for line in f:
            lineobj = json.loads(line)
            source_meta[lineobj["source_id"]] = lineobj

    # find all subdirectories in poor_path
    poor_dirs = list(poor_path.glob("**/*"))
    poor_dirs = [poor_dir for poor_dir in poor_dirs if poor_dir.is_dir()]

    # Create output path in parent directory with .jsonl suffix
    output_path = poor_path.parent / f"{language}_{source}_poor.jsonl"

    yaml_parser = YAML()
    yaml_parser.preserve_quotes = True  # Preserve original formatting

    with open(output_path, "w") as f:
        yaml_files_id = []
        for poor_dir in poor_dirs:
            # Find all .yaml files in the directory (recursively)
            yaml_files = list(poor_dir.glob("*.yaml"))
            yaml_files_id.extend(
                [
                    {
                        "id": get_vericoding_id(
                            source, language, yaml_file.stem, source_meta
                        ),
                        "path": yaml_file,
                    }
                    for yaml_file in yaml_files
                ]
            )

        yaml_files_id = natsorted(yaml_files_id, key=lambda x: x["id"])

        if not yaml_files:
            print(f"No .yaml files found in {poor_dir}")
            return

        processed_count = 0
        skipped_count = 0

        for yaml_file_id in yaml_files_id:
            id = yaml_file_id["id"]
            yaml_file = yaml_file_id["path"]
            try:
                # Load the YAML spec
                spec = yaml_parser.load(yaml_file)

                # Validate that spec is a dictionary
                if not isinstance(spec, dict):
                    print(
                        f"Warning: {yaml_file} does not contain a YAML dictionary, skipping"
                    )
                    skipped_count += 1
                    continue

                # Create a new dictionary with id field first
                new_spec = {
                    "id": id,
                    "language": language,
                    "source": source,
                    "source_id": yaml_file.stem,
                }
                new_spec.update(spec)
                new_spec["qa-issue"] = 1
                new_spec["qa-issue-type"] = poor_dir.name

                # Write as JSON line
                json.dump(new_spec, f, ensure_ascii=False)
                f.write("\n")
                processed_count += 1

            except YAMLError as e:
                print(
                    f"Warning: Failed to parse {yaml_file} as YAML (likely contains raw code instead of YAML): {e}"
                )
                skipped_count += 1
                continue

    print(f"Converted {processed_count} YAML files to {output_path}")
    if skipped_count > 0:
        print(f"Skipped {skipped_count} files that were not valid YAML")


def convert_yaml_to_dir(
    suffix: str, yaml_path: Path, output_path: Path = None, add_postamble: bool = False
) -> None:
    """Convert all YAML files in a directory to a new directory with specified suffix.

    Args:
        suffix: File suffix for the output files
        yaml_path: Path to the input YAML directory
        output_path: Output directory path (optional)
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")

    # Find all .yaml files in the directory (recursively)
    yaml_files = list(yaml_path.glob("**/*.yaml"))

    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return

    # Create output directory path
    if output_path is None:
        output_dir = yaml_path.parent / f"{yaml_path.name}_{suffix}"
    else:
        output_dir = output_path

    # Delete the output directory recursively if it exists, then create a new one
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    if suffix in ["lean", "dfy", "rs"]:
        for yaml_file in yaml_files:
            # Preserve directory structure in output
            relative_path = yaml_file.relative_to(yaml_path)
            output_file = output_dir / relative_path.with_suffix(f".{suffix}")
            # Ensure the output directory exists
            output_file.parent.mkdir(parents=True, exist_ok=True)
            convert_yaml_to_file(yaml_file, output_file, add_postamble)

    elif suffix == "json":
        for yaml_file in yaml_files:
            # Preserve directory structure in output
            relative_path = yaml_file.relative_to(yaml_path)
            output_file = output_dir / relative_path.with_suffix(f".{suffix}")
            # Ensure the output directory exists
            output_file.parent.mkdir(parents=True, exist_ok=True)
            convert_yaml_to_json(yaml_file, output_file)

    else:
        raise ValueError(f"Unsupported suffix: {suffix}")

    print(f"Converted {len(yaml_files)} YAML files to {output_dir}")


def convert_jsonl_to_dir(
    suffix: str, jsonl_path: Path, output_path: Path = None, add_postamble: bool = False
) -> None:
    """Convert all entries in a JSONL file to individual files with specified suffix.

    Args:
        suffix: File suffix for the output files
        jsonl_path: Path to the JSONL file
        output_path: Output directory path (optional)
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    if not jsonl_path.is_file():
        raise ValueError(f"{jsonl_path} is not a file")

    # Create output directory path
    if output_path is None:
        output_dir = jsonl_path.parent / f"{jsonl_path.stem}_{suffix}"
    else:
        output_dir = output_path

    # Delete the output directory recursively if it exists, then create a new one
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True)

    # Read JSONL file and process each line
    processed_count = 0
    with open(jsonl_path, "r") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:  # Skip empty lines
                continue

            try:
                # Parse JSON line
                spec = json.loads(line)

                # Check if id field exists
                if "source_id" not in spec:
                    print(f"Warning: Line {line_num} missing 'id' field, skipping")
                    continue

                file_id = spec["source_id"]

                if suffix in ["lean", "dfy", "rs"]:
                    # Reconstruct directory structure from the file_id (which contains relative path)
                    output_file = output_dir / f"{file_id}.{suffix}"
                    # Ensure the output directory exists
                    output_file.parent.mkdir(parents=True, exist_ok=True)
                    convert_spec_to_file(spec, output_file, add_postamble)

                elif suffix == "json":
                    # Reconstruct directory structure from the file_id (which contains relative path)
                    output_file = output_dir / f"{file_id}.{suffix}"
                    # Ensure the output directory exists
                    output_file.parent.mkdir(parents=True, exist_ok=True)
                    with open(output_file, "w") as out_f:
                        json.dump(spec, out_f, ensure_ascii=False, indent=2)

                else:
                    raise ValueError(f"Unsupported suffix: {suffix}")

                processed_count += 1

            except json.JSONDecodeError as e:
                print(f"Warning: Invalid JSON on line {line_num}: {e}")
                continue

    if processed_count == 0:
        print(f"No valid entries found in {jsonl_path}")
    else:
        print(f"Converted {processed_count} entries from {jsonl_path} to {output_dir}")


def process_bench(
    bench_dir: Path, suffix: str = None, add_postamble: bool = False
) -> None:
    """Process a single benchmark directory to convert YAML files.

    Args:
        bench_dir: Path to the benchmark directory (should contain a 'yaml' subdirectory)
        suffix: File suffix for the output files (e.g., 'dfy', 'lean', 'rs').
                If None, auto-detects from parent directory structure.
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).

    Creates:
        1. A JSONL file in the benchmark directory with naming pattern: XXX_YYY.jsonl
        2. A 'files' folder in the benchmark directory with individual files
    """

    # Validate bench_dir
    if not bench_dir.exists():
        raise FileNotFoundError(f"Benchmark directory {bench_dir} does not exist")

    if not bench_dir.is_dir():
        raise ValueError(f"{bench_dir} is not a directory")

    # Construct yaml_dir path
    yaml_dir = bench_dir / "yaml"

    # Validate yaml_dir exists
    if not yaml_dir.exists():
        raise FileNotFoundError(f"YAML directory {yaml_dir} does not exist")

    if not yaml_dir.is_dir():
        raise ValueError(f"{yaml_dir} is not a directory")

    # Get the parent directory (level1_dir) for suffix detection
    level1_dir = bench_dir.parent

    level1_name = level1_dir.name
    level2_name = bench_dir.name

    # Determine suffix - use provided suffix or auto-detect from parent directory
    if suffix is not None:
        bench_suffix = suffix
    else:
        # Auto-detect suffix from parent directory structure
        if level1_name == "dafny":
            bench_suffix = "dfy"
        elif level1_name == "lean":
            bench_suffix = "lean"
        elif level1_name == "verus":
            bench_suffix = "rs"
        else:
            raise ValueError(
                f"Unknown benchmark type '{level1_name}'. Expected 'dafny', 'lean', or 'verus'. Use suffix parameter to specify manually."
            )

    print(f"Processing {bench_dir} with suffix '{bench_suffix}'...")

    # 1. Convert all YAML files to JSONL using custom naming: XXX_YYY.jsonl
    jsonl_path = bench_dir / f"{level1_name}_{level2_name}.jsonl"
    convert_yaml_to_jsonl(
        yaml_dir, language=level1_name, source=level2_name, jsonl_path=jsonl_path
    )

    # 2. Convert JSONL to individual files in 'files' folder (only if JSONL was created)
    if jsonl_path.exists():
        files_dir = bench_dir / "files"
        convert_jsonl_to_dir(bench_suffix, jsonl_path, files_dir, add_postamble)
    else:
        print(f"No JSONL file created, skipping file conversion for {bench_dir}")


def process_poor(
    bench_dir: Path, suffix: str = None, add_postamble: bool = False
) -> None:
    """Process a single benchmark directory to convert POOR files.

    Args:
        bench_dir: Path to the benchmark directory (should contain a 'yaml' subdirectory)
        suffix: File suffix for the output files (e.g., 'dfy', 'lean', 'rs').
                If None, auto-detects from parent directory structure.
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).

    Creates:
        1. A JSONL file in the benchmark directory with naming pattern: XXX_YYY.jsonl
        2. A 'files' folder in the benchmark directory with individual files
    """

    # Validate bench_dir
    if not bench_dir.exists():
        raise FileNotFoundError(f"Benchmark directory {bench_dir} does not exist")

    if not bench_dir.is_dir():
        raise ValueError(f"{bench_dir} is not a directory")

    # Construct poor_dir path
    poor_dir = bench_dir / "poor"

    # Validate yaml_dir exists
    if not poor_dir.exists():
        raise FileNotFoundError(f"POOR directory {poor_dir} does not exist")

    if not poor_dir.is_dir():
        raise ValueError(f"{poor_dir} is not a directory")

    # Get the parent directory (level1_dir) for suffix detection
    level1_dir = bench_dir.parent

    level1_name = level1_dir.name
    level2_name = bench_dir.name

    # Determine suffix - use provided suffix or auto-detect from parent directory
    if suffix is not None:
        bench_suffix = suffix
    else:
        # Auto-detect suffix from parent directory structure
        if level1_name == "dafny":
            bench_suffix = "dfy"
        elif level1_name == "lean":
            bench_suffix = "lean"
        elif level1_name == "verus":
            bench_suffix = "rs"
        else:
            raise ValueError(
                f"Unknown benchmark type '{level1_name}'. Expected 'dafny', 'lean', or 'verus'. Use suffix parameter to specify manually."
            )

    print(f"Processing {bench_dir} with suffix '{bench_suffix}'...")

    # 1. Convert all YAML files to JSONL using custom naming: XXX_YYY.jsonl
    jsonl_path = bench_dir / f"{level1_name}_{level2_name}_poor.jsonl"
    convert_poor_to_jsonl(
        poor_dir, language=level1_name, source=level2_name, jsonl_path=jsonl_path
    )

    # 2. Convert JSONL to individual files in 'files' folder (only if JSONL was created)
    if jsonl_path.exists():
        issues_dir = bench_dir / "issues"
        convert_jsonl_to_dir(bench_suffix, jsonl_path, issues_dir, add_postamble)
    else:
        print(f"No JSONL file created, skipping file conversion for {bench_dir}")


def process_all_poor(
    benchmarks_dir: Path, suffix: str = None, add_postamble: bool = False
) -> None:
    """Process benchmark directories to convert POOR files.

    For each level-2 subfolder of benchmarks/XXX/YYY:
    1. Look for a 'poor' folder
    2. If it exists, convert POOR files to files with the appropriate suffix in 'issues' folder
       (suffix determined by XXX: dafny->dfy, lean->lean, verus->rs)
    3. Convert all POOR files to a JSONL file using custom naming: XXX_YYY_poor.jsonl

    Args:
        benchmarks_dir: Path to the benchmarks directory
        suffix: File suffix for the output files (optional, auto-detected if None)
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")

    if not benchmarks_dir.is_dir():
        raise ValueError(f"{benchmarks_dir} is not a directory")

    # Find all level-2 subdirectories (benchmarks/XXX/YYY)
    level2_dirs = []
    for level1_dir in benchmarks_dir.iterdir():
        if level1_dir.is_dir():
            for level2_dir in level1_dir.iterdir():
                if level2_dir.is_dir():
                    yaml_dir = level2_dir / "poor"
                    if yaml_dir.exists():
                        level2_dirs.append(level2_dir)

    if not level2_dirs:
        print(f"No level-2 subdirectories found in {benchmarks_dir} with poor folder")
        return

    processed_count = 0

    for level2_dir in level2_dirs:
        # Determine suffix based on level-1 directory name (XXX)
        level1_name = level2_dir.parent.name
        if suffix is None:
            if level1_name == "dafny":
                dir_suffix = "dfy"
            elif level1_name == "lean":
                dir_suffix = "lean"
            elif level1_name == "verus":
                dir_suffix = "rs"
            else:
                raise ValueError(
                    f"Unknown benchmark type '{level1_name}'. Expected 'dafny', 'lean', or 'verus'"
                )
        else:
            dir_suffix = suffix

        # Use the new process_bench function
        process_poor(level2_dir, dir_suffix, add_postamble)
        processed_count += 1

    print(f"Processed {processed_count} benchmark directories with poor folder")


def flatten_task_with_entry_qa(task: Dict[str, Any]) -> Dict[str, Any]:
    """Flatten a task with entry qa."""
    new_task = {
        "id": task["id"],
        "language": task["language"],
        "source": task["source"],
        "source-id": task["source_id"],
        "source-notes": "",
        "vc-description": "",
        "vc-preamble": "",
        "vc-helpers": "",
    }

    if task["language"] in ["dafny", "verus"]:
        new_task.update(
            {
                "vc-spec": "",
                "vc-code": "",
            }
        )
    elif task["language"] == "lean":
        new_task.update(
            {
                "vc-definitions": "",
                "vc-theorems": "",
            }
        )

    new_task.update({"vc-postamble": ""})
    new_task.update({"qa-issue": 0})
    new_task.update({"qa-issue-type": ""})

    if task["language"] == "dafny":
        new_task.update(
            {
                "qa-functions-with-default-values": -1,
                "qa-methods-with-bodies": -1,
            }
        )
    elif task["language"] == "verus":
        new_task.update(
            {
                "qa-specs-with-default-values": -1,
                "qa-execs-with-bodies": -1,
                "qa-execs-with-ghost-types": -1,
            }
        )
    elif task["language"] == "lean":
        new_task.update(
            {
                "qa-definitions-with-sorry": -1,
            }
        )

    new_task.update(
        {
            "qa-near-duplicate-group": "",
            "qa-score": -1,
        }
    )

    if "vc-description" in task:
        new_task["vc-description"] = task["vc-description"]
    if "vc-preamble" in task:
        new_task["vc-preamble"] = task["vc-preamble"]
    if "vc-helpers" in task:
        new_task["vc-helpers"] = task["vc-helpers"]
    if "vc-spec" in task:
        new_task["vc-spec"] = task["vc-spec"]
    if "vc-code" in task:
        new_task["vc-code"] = task["vc-code"]
    if "vc-definitions" in task:
        new_task["vc-definitions"] = task["vc-definitions"]
    if "vc-theorems" in task:
        new_task["vc-theorems"] = task["vc-theorems"]
    if "vc-postamble" in task:
        new_task["vc-postamble"] = task["vc-postamble"]

    if "qa_entry_metadata" in task:
        issues = task["qa_entry_metadata"]["issues"]
        if "functions_with_default_values" in issues:
            new_task["qa-functions-with-default-values"] = issues[
                "functions_with_default_values"
            ]
        if "methods_with_bodies" in issues:
            new_task["qa-methods-with-bodies"] = issues["methods_with_bodies"]
        if "specs-with-default-values" in issues:
            new_task["qa-specs-with-default-values"] = issues[
                "specs-with-default-values"
            ]
        if "execs-with-bodies" in issues:
            new_task["qa-execs-with-bodies"] = issues["execs-with-bodies"]
        if "execs-with-ghost-types" in issues:
            new_task["qa-execs-with-ghost-types"] = issues["execs-with-ghost-types"]
        if "definitions-with-sorry" in issues:
            new_task["qa-definitions-with-sorry"] = issues["definitions-with-sorry"]
        new_task["qa-score"] = task["qa_entry_metadata"]["individual_score"]

    return new_task


def process_language_tasks(benchmarks_dir: Path) -> None:
    """Process benchmark directories to convert YAML files.

    For each level-2 subfolder of benchmarks/XXX/YYY:
    1. Look for a 'yaml' folder
    2. If it exists, convert YAML files to files with the appropriate suffix in 'files' folder
       (suffix determined by XXX: dafny->dfy, lean->lean, verus->rs)
    3. Convert all YAML files to a JSONL file using custom naming: XXX_YYY.jsonl

    Args:
        benchmarks_dir: Path to the benchmarks directory
        suffix: File suffix for the output files (optional, auto-detected if None)
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")

    if not benchmarks_dir.is_dir():
        raise ValueError(f"{benchmarks_dir} is not a directory")

    for language in ["dafny", "lean", "verus"]:
        language_dir = benchmarks_dir / language
        if not language_dir.exists():
            raise FileNotFoundError(f"Language directory {language_dir} does not exist")
        if not language_dir.is_dir():
            raise ValueError(f"{language_dir} is not a directory")

        # get all subdirectories in language_dir
        source_dirs = list(language_dir.iterdir())
        source_dirs = [source_dir for source_dir in source_dirs if source_dir.is_dir()]
        source_dirs = sorted(source_dirs, key=lambda x: sources_ref[x.name])

        # generate language tasks file
        output_tasks = benchmarks_dir / f"{language}_tasks.jsonl"
        with open(output_tasks, "w") as f:
            for source_dir in source_dirs:
                source = source_dir.name
                no_qa_file = source_dir / f"{language}_{source}.jsonl"
                qa_one_file = source_dir / f"{language}_{source}_with_entry_qa.jsonl"
                qa_all_file = source_dir / f"{language}_{source}.metadata.json"
                if not qa_one_file.exists():
                    if no_qa_file.exists():
                        qa_one_file = no_qa_file
                    else:
                        raise FileNotFoundError(
                            f"Files {qa_one_file} and {no_qa_file} does not exist"
                        )

                # check if no_qa_file and qa_one_file have the same lines
                with open(no_qa_file, "r") as g:
                    no_qa_lines = [json.loads(line) for line in g]
                with open(qa_one_file, "r") as g:
                    qa_one_lines = [json.loads(line) for line in g]
                for dict1, dict2 in zip(no_qa_lines, qa_one_lines):
                    for key in dict1:
                        if dict1[key] != dict2[key]:
                            dict2[key] = dict1[key]
                            print(
                                f"WARNING: In files {no_qa_file} and {qa_one_file}, {key} is different. Replacing with value from {no_qa_file}."
                            )
                            # raise ValueError(f"Files {no_qa_file} and {qa_one_file} have different lines:\n{dict1[key]} \n{dict2[key]}")

                # write qa_one_file to file
                with open(qa_one_file, "w") as g:
                    for dict in qa_one_lines:
                        json.dump(dict, g, ensure_ascii=False)
                        g.write("\n")

                # read tasks file as jsonl into a list of dictionaries
                tasks = {}
                with open(qa_one_file, "r") as g:
                    for line in g:
                        task = flatten_task_with_entry_qa(json.loads(line))
                        tasks[task["source-id"]] = task

                if not qa_all_file.exists():
                    print(f"QA file {qa_all_file} does not exist")
                else:
                    # read qa_all_file as json into a dictionary
                    with open(qa_all_file, "r") as g:
                        qa_all_dict = json.load(g)

                    # get duplicate tasks and assign group IDs
                    duplicates = qa_all_dict["qa_metadata"]["near_duplicates"][
                        "examples"
                    ]
                    for idx, dup_grp in enumerate(duplicates):
                        # make group_id 4 characters long
                        group_id = f"Dup{languages_ref[language]}{sources_ref[source]}{idx:02d}"
                        for file in dup_grp["files"]:
                            tasks[Path(file).stem]["qa-near-duplicate-group"] = group_id

                # write tasks to file
                for task in tasks.values():
                    json.dump(task, f, ensure_ascii=False)
                    f.write("\n")
        print(f"Wrote tasks file {output_tasks}")

        # generate language issues file
        output_issues = benchmarks_dir / f"{language}_issues.jsonl"
        with open(output_issues, "w") as f:
            for source_dir in source_dirs:
                issues_file = source_dir / f"{language}_{source_dir.name}_poor.jsonl"
                if not issues_file.exists():
                    print(f"Issues file {issues_file} does not exist")
                else:
                    with open(issues_file, "r") as g:
                        issues = [
                            flatten_task_with_entry_qa(json.loads(line)) for line in g
                        ]
                    for issue in issues:
                        json.dump(issue, f, ensure_ascii=False)
                        f.write("\n")
        print(f"Wrote issues file {output_issues}")

    print("Generated tasks and issues files for all languages")


def process_benchmarks(
    benchmarks_dir: Path, suffix: str = None, add_postamble: bool = False
) -> None:
    """Process benchmark directories to convert YAML files.

    For each level-2 subfolder of benchmarks/XXX/YYY:
    1. Look for a 'yaml' folder
    2. If it exists, convert YAML files to files with the appropriate suffix in 'files' folder
       (suffix determined by XXX: dafny->dfy, lean->lean, verus->rs)
    3. Convert all YAML files to a JSONL file using custom naming: XXX_YYY.jsonl

    Args:
        benchmarks_dir: Path to the benchmarks directory
        suffix: File suffix for the output files (optional, auto-detected if None)
        add_postamble: If True, include vc-postamble in the template (default: omit for Lean, include for others).
    """

    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")

    if not benchmarks_dir.is_dir():
        raise ValueError(f"{benchmarks_dir} is not a directory")

    # Find all level-2 subdirectories (benchmarks/XXX/YYY)
    level2_dirs = []
    for level1_dir in benchmarks_dir.iterdir():
        if level1_dir.is_dir():
            for level2_dir in level1_dir.iterdir():
                if level2_dir.is_dir():
                    yaml_dir = level2_dir / "yaml"
                    if yaml_dir.exists():
                        level2_dirs.append(level2_dir)

    if not level2_dirs:
        print(f"No level-2 subdirectories found in {benchmarks_dir}")
        return

    processed_count = 0

    for level2_dir in level2_dirs:
        # Determine suffix based on level-1 directory name (XXX)
        level1_name = level2_dir.parent.name
        if suffix is None:
            if level1_name == "dafny":
                dir_suffix = "dfy"
            elif level1_name == "lean":
                dir_suffix = "lean"
            elif level1_name == "verus":
                dir_suffix = "rs"
            else:
                raise ValueError(
                    f"Unknown benchmark type '{level1_name}'. Expected 'dafny', 'lean', or 'verus'"
                )
        else:
            dir_suffix = suffix

        # Use the new process_bench function
        process_bench(level2_dir, dir_suffix, add_postamble)
        processed_count += 1

    print(f"Processed {processed_count} benchmark directories")


def spec_to_yaml(
    spec: dict, yaml_path: Path, recommended_keys: list[str] = None
) -> None:
    """Write a spec dictionary to a YAML file with proper multiline string formatting.

    Args:
        spec: Dictionary containing the spec data
        yaml_path: Path to the output YAML file
        recommended_keys: List of keys that should be present in spec, in the order they should appear in the YAML file.
                      If None, writes all keys in arbitrary order without validation.
    """

    # Validate recommended keys if provided
    if recommended_keys is not None:
        # Check for missing recommended keys
        missing_keys = [key for key in recommended_keys if key not in spec]
        if missing_keys:
            raise ValueError(f"Missing recommended keys in spec: {missing_keys}")

        # Check for extra keys not in recommended list
        extra_keys = [key for key in spec.keys() if key not in recommended_keys]
        if extra_keys:
            raise ValueError(
                f"Spec contains keys not in recommended list: {extra_keys}"
            )

        # Use recommended_keys for ordering
        keys_to_write = recommended_keys
    else:
        # Use all keys in arbitrary order
        keys_to_write = list(spec.keys())

    # Manually write the YAML file with multiline strings
    with open(yaml_path, "w") as f:
        for key in keys_to_write:
            value = spec[key]
            # Write the key with multiline indicator
            f.write(f"{key}: |-\n")

            # Write the value in multiline format
            if isinstance(value, str):
                stripped_value = value.rstrip()
                if stripped_value:
                    # Split into lines and add two spaces to each line
                    lines = stripped_value.split("\n")
                    for line in lines:
                        f.write("  " + line + "\n")
                    f.write("\n")
                else:
                    f.write("\n")
            else:
                raise ValueError(f"Unsupported value type: {type(value)}")


def clear_implementation(yaml_path: Path) -> None:
    """Read a YAML file, replace vc-implementation, vc-proof, and vc-code fields with empty strings, and write back."""

    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting

    # Load the YAML file
    with open(yaml_path, "r") as f:
        spec = yaml.load(f)

    # Replace the specified fields with empty strings
    fields_to_clear = ["vc-implementation", "vc-proof"]
    for field in fields_to_clear:
        if field in spec:
            spec[field] = "-- <" + field + ">\n  sorry\n-- </" + field + ">\n\n"

    # Write the modified spec back to YAML
    # Get recommended keys in the order they appeared in the original file
    # Thankfully ruamel.yaml preserves the order of keys when loading
    recommended_keys = [key for key in spec.keys()]
    spec_to_yaml(spec, yaml_path, recommended_keys=recommended_keys)

    print(f"Cleared implementation fields in {yaml_path}")


def get_source_meta(benchmarks_dir: Path, save_path: Path = None) -> Dict[str, Any]:
    """Get metadata about files in the benchmarks directory."""

    # Initialize the main metadata object
    if save_path and save_path.exists():
        with open(save_path, "r") as f:
            source_meta = json.load(f)
    else:
        source_meta = {}

    source_meta: Dict[str, Any] = {}

    # Iterate through each XXX folder (lean, dafny, verus)
    for xxx_dir in benchmarks_dir.iterdir():
        if not xxx_dir.is_dir() or xxx_dir.name.startswith("."):
            continue

        xxx_name = xxx_dir.name
        if xxx_name not in ["lean", "dafny", "verus"]:
            raise ValueError(
                f"Unknown benchmark type '{xxx_name}'. Expected 'lean', 'dafny', or 'verus'."
            )
        # print(f"Processing {xxx_name} directory...")

        # Iterate through each YYY subfolder
        for yyy_dir in xxx_dir.iterdir():
            if not yyy_dir.is_dir() or yyy_dir.name.startswith("."):
                continue

            yyy_name = yyy_dir.name

            # Validate that the YYY subdirectory is either "poor", "yaml", or "files"
            for yyy_subdir in yyy_dir.iterdir():
                if not yyy_subdir.is_dir() or yyy_subdir.name.startswith("."):
                    continue

                yyy_subdir_name = yyy_subdir.name
                if yyy_subdir_name not in ["poor", "yaml", "files", "issues"]:
                    raise ValueError(
                        f"Unknown benchmark type '{yyy_subdir_name}' in {yyy_dir}. Expected 'poor' or 'yaml' or 'files'."
                    )

            yaml_dir = yyy_dir / "yaml"
            poor_dir = yyy_dir / "poor"

            # Check if yaml directory exists
            if not yaml_dir.exists():
                print(f"Warning: No yaml directory found in {yyy_dir}")
                continue

            if not yaml_dir.is_dir():
                raise NotADirectoryError(f"{yaml_dir} is not a directory")

            # print(f"  Processing {yyy_name} subdirectory...")

            # Get all files in the yaml directory
            yaml_files = list(yaml_dir.iterdir())

            # Validate that all files are .yaml files
            for file_path in yaml_files:
                if not file_path.is_file():
                    raise ValueError(f"{file_path} is not a file")
                if not file_path.name.endswith(".yaml"):
                    raise ValueError(f"{file_path} is not a .yaml file")
                if " " in file_path.name:
                    raise ValueError(f"{file_path} contains spaces in filename")

            # Process each YAML file
            for yaml_file in yaml_files:
                # Extract the base name (ZZZ) from ZZZ.yaml
                zzz_name = yaml_file.stem  # This removes the .yaml extension

                # Check if ZZZ is a key in source_meta
                if zzz_name not in source_meta:
                    # Initialize SM[XXX][YYY] = "" for YYY in [Lean, Dafny, Verus]
                    source_meta[zzz_name] = {"lean": "", "dafny": "", "verus": ""}

                v = source_meta[zzz_name]

                # Insert the key-value (XXX, "yaml") to V
                v[xxx_name] = "yaml"

                # Check if "source" is a key of V
                if "source" in v:
                    if v["source"] != yyy_name:
                        raise ValueError(
                            f"Inconsistent source for {zzz_name}. "
                            f"Expected {v['source']}, found {yyy_name}"
                        )
                else:
                    # Insert the key-value ("source", YYY) to V
                    v["source"] = yyy_name

            # Process poor directory if it exists
            if poor_dir.exists() and poor_dir.is_dir():
                # print(f"  Processing poor directory in {yyy_name}...")

                # Check for any files that are not directories and don't start with "."
                for item in poor_dir.iterdir():
                    if item.is_file() and not item.name.startswith("."):
                        raise ValueError(
                            f"Found unexpected file in poor directory: {item}. "
                            f"Only directories are allowed in poor directory."
                        )

                # Iterate through each ZZZ folder in poor directory
                for zzz_dir in poor_dir.iterdir():
                    if not zzz_dir.is_dir() or zzz_dir.name.startswith("."):
                        continue

                    zzz_name = zzz_dir.name
                    # print(f"    Processing poor/{zzz_name} folder...")

                    # Get all files in the ZZZ folder
                    zzz_files = list(zzz_dir.iterdir())
                    for www_file in zzz_files:
                        if not www_file.is_file() or www_file.name.startswith("."):
                            raise ValueError(
                                f"Found unexpected file in poor directory: {www_file}. "
                            )
                        if not www_file.name.endswith(".yaml"):
                            if zzz_dir.name not in ["unformatted"]:
                                raise ValueError(
                                    f"{www_file} in {zzz_dir} is not a .yaml file"
                                )

                        # Case 1: WWW is of the form UUU.yaml
                        uuu_name = www_file.stem  # Remove .yaml extension

                        # Check if UUU is already in source_meta
                        if uuu_name in source_meta:
                            # Raise error if SM[UUU][XXX] starts with "yaml"
                            if source_meta[uuu_name][xxx_name].startswith("yaml"):
                                raise ValueError(
                                    f"SM[{uuu_name}][{xxx_name}] starts with 'yaml' but file is poor; "
                                    f"path: {www_file}, "
                                    f"found: {source_meta[uuu_name][xxx_name]}"
                                )
                        else:
                            # Create entry SM[UUU] with empty strings for all languages
                            source_meta[uuu_name] = {
                                "lean": "",
                                "dafny": "",
                                "verus": "",
                            }

                        # Set SM[UUU][XXX] to "poor/ZZZ"
                        source_meta[uuu_name][xxx_name] = f"poor/{zzz_name}"

                        # Set source if not already set
                        if "source" not in source_meta[uuu_name]:
                            source_meta[uuu_name]["source"] = yyy_name
                        elif source_meta[uuu_name]["source"] != yyy_name:
                            raise ValueError(
                                f"Inconsistent source for {uuu_name}. "
                                f"Expected {source_meta[uuu_name]['source']}, found {yyy_name}"
                            )

    print(f"\nTotal files processed: {len(source_meta)}")

    source_meta = generate_ids(source_meta)

    # save as jsonl file
    if save_path:
        with open(save_path, "w") as f:
            for key, value in source_meta.items():
                json.dump(
                    {
                        "id": value["id"],
                        "source": value["source"],
                        "source_id": key,
                        "dafny": value["dafny"],
                        "lean": value["lean"],
                        "verus": value["verus"],
                    },
                    f,
                    ensure_ascii=False,
                )
                f.write("\n")
        print(f"Metadata saved to: {save_path}")

    return source_meta


def get_all_sources(source_meta: Dict[str, Any]) -> set[str]:
    """Get all possible sources from source_meta.

    Args:
        source_meta: Dictionary containing file metadata

    Returns:
        Set of all unique source values found in source_meta
    """
    sources = set()
    for file_data in source_meta.values():
        if "source" in file_data:
            sources.add(file_data["source"])
    return sources


def count_files_by_source(source_meta: Dict[str, Any]) -> Dict[str, Dict[str, int]]:
    """Count files by source and language type.

    For each source in source_meta, counts:
    1. Total number of filenames with that source
    2. Total number of Lean filenames with that source
    3. Total number of Dafny filenames with that source
    4. Total number of Verus filenames with that source

    Args:
        source_meta: Dictionary containing file metadata

    Returns:
        Dictionary mapping source names to counts of different file types
    """
    source_counts = {}

    for filename, file_data in source_meta.items():
        source = file_data.get("source")
        if source is None:
            continue

        # Initialize source entry if not exists
        if source not in source_counts:
            source_counts[source] = {
                "total": 0,
                "lean": {"yaml": 0, "poor": 0},
                "dafny": {"yaml": 0, "poor": 0},
                "verus": {"yaml": 0, "poor": 0},
            }

        # Count total files for this source
        source_counts[source]["total"] += 1

        # Count files by language type (check for non-empty string values)
        if "lean" in file_data and file_data["lean"].startswith("yaml"):
            source_counts[source]["lean"]["yaml"] += 1
        if "dafny" in file_data and file_data["dafny"].startswith("yaml"):
            source_counts[source]["dafny"]["yaml"] += 1
        if "verus" in file_data and file_data["verus"].startswith("yaml"):
            source_counts[source]["verus"]["yaml"] += 1
        if "lean" in file_data and file_data["lean"].startswith("poor"):
            source_counts[source]["lean"]["poor"] += 1
        if "dafny" in file_data and file_data["dafny"].startswith("poor"):
            source_counts[source]["dafny"]["poor"] += 1
        if "verus" in file_data and file_data["verus"].startswith("poor"):
            source_counts[source]["verus"]["poor"] += 1

    return source_counts


def validate_source_signatures(source_meta: Dict[str, Any]) -> None:
    """Validate that all entries for each source have the same signature.

    For each source, filters out all entries from source_meta with that source,
    then checks that all the filtered entries have the same (Lean, Verus, Dafny) signature.
    Prints out all files with inconsistent signatures.

    Args:
        source_meta: Dictionary containing file metadata
    """
    sources = get_all_sources(source_meta)
    inconsistent_files = []

    for source in sources:
        # Filter entries for this source
        source_entries = {
            filename: data
            for filename, data in source_meta.items()
            if data.get("source") == source
        }

        if not source_entries:
            continue

        # Get the signature (set of languages with non-empty values) for the first entry
        first_entry = next(iter(source_entries.values()))
        expected_signature = set(
            key
            for key in first_entry.keys()
            if key in ["lean", "dafny", "verus"] and first_entry[key]
        )

        # Check that all other entries have the same signature
        for filename, entry_data in source_entries.items():
            entry_signature = set(
                key
                for key in entry_data.keys()
                if key in ["lean", "dafny", "verus"] and entry_data[key]
            )
            if entry_signature != expected_signature:
                inconsistent_files.append(
                    {
                        "source": source,
                        "filename": filename,
                        "actual_signature": sorted(entry_signature),
                        "expected_signature": sorted(expected_signature),
                    }
                )

    # Print all inconsistent files
    if inconsistent_files:
        print("\nFiles with inconsistent signatures:")
        print("=" * 50)
        for item in inconsistent_files:
            print(
                f"Source: {item['source']} File: {item['filename']} {item['expected_signature']} {item['actual_signature']}"
            )
    else:
        print("\nAll files have consistent signatures for their sources.")


def print_summary_counts(source_meta: Dict[str, Any]) -> None:
    """Print total counts of files by source and language type."""

    # Initialize totals
    total = {}
    for novelty in ["all", "novel"]:
        total[novelty] = {}
        for lang in ["lean", "dafny", "verus"]:
            total[novelty][lang] = {}
            for file_type in ["yaml", "poor"]:
                total[novelty][lang][file_type] = 0

    # Count files by source and language type
    source_counts = count_files_by_source(source_meta)

    # Print counts for each source and accumulate totals
    print("\nFile counts by source:")
    print("=" * 50)
    for source, counts in sorted(source_counts.items()):
        print(f"Source: {source}")
        print(f"  Total files: {counts['total']}")
        print(
            f"  Dafny files: {counts['dafny']['yaml'] + counts['dafny']['poor']} : {counts['dafny']['yaml']} "
        )
        print(
            f"  Verus files: {counts['verus']['yaml'] + counts['verus']['poor']} : {counts['verus']['yaml']} "
        )
        print(
            f"  Lean files: {counts['lean']['yaml'] + counts['lean']['poor']} : {counts['lean']['yaml']} "
        )
        print(
            f"  Subtotals: {
                counts['lean']['yaml']
                + counts['dafny']['yaml']
                + counts['verus']['yaml']
                + counts['lean']['poor']
                + counts['dafny']['poor']
                + counts['verus']['poor']
            } : {
                counts['lean']['yaml']
                + counts['dafny']['yaml']
                + counts['verus']['yaml']
            } "
        )
        print()

        # Accumulate totals
        for lang in ["lean", "dafny", "verus"]:
            for file_type in ["yaml", "poor"]:
                total["all"][lang][file_type] += counts[lang][file_type]
                total["novel"][lang][file_type] += counts[lang][file_type] * (
                    0 if (lang, source) in not_novel else 1
                )

    # Print grand totals
    print("=" * 50)
    print("GRAND TOTALS")
    print("=" * 50)
    print(
        f"Dafny total (all): {total['all']['dafny']['yaml'] + total['all']['dafny']['poor']} : {total['all']['dafny']['yaml']}"
    )
    print(
        f"Verus total (all): {total['all']['verus']['yaml'] + total['all']['verus']['poor']} : {total['all']['verus']['yaml']}"
    )
    print(
        f"Lean total (all): {total['all']['lean']['yaml'] + total['all']['lean']['poor']} : {total['all']['lean']['yaml']}"
    )
    print(
        f"Dafny total (novel): {total['novel']['dafny']['yaml'] + total['novel']['dafny']['poor']} : {total['novel']['dafny']['yaml']}"
    )
    print(
        f"Verus total (novel): {total['novel']['verus']['yaml'] + total['novel']['verus']['poor']} : {total['novel']['verus']['yaml']}"
    )
    print(
        f"Lean total (novel): {total['novel']['lean']['yaml'] + total['novel']['lean']['poor']} : {total['novel']['lean']['yaml']}"
    )
    print("=" * 50)

    # Print grand totals
    grand_total = {}
    for novelty in ["all", "novel"]:
        grand_total[novelty] = {}
        for file_type in ["yaml", "poor"]:
            grand_total[novelty][file_type] = 0
            for lang in ["lean", "dafny", "verus"]:
                grand_total[novelty][file_type] += total[novelty][lang][file_type]

    print(
        f"Grand total (all):  {grand_total['all']['yaml'] + grand_total['all']['poor']} : {grand_total['all']['yaml']}"
    )
    print(
        f"Grand total (novel): {grand_total['novel']['yaml'] + grand_total['novel']['poor']} : {grand_total['novel']['yaml']}"
    )
    print("=" * 50)

    # randomly pick a source, a language, and a task, and print the Vericoding ID
    # import random
    # for _ in range(10):
    #     language = random.choice(list(languages_ref.keys()))
    #     task = random.choice(list(source_meta.keys()))
    #     source = source_meta[task]['source']
    #     print(f"Vericoding ID: {get_vericoding_id(source, language, task, source_meta)}")
    #     print(f"Source: {source}")
    #     print(f"Language: {language}")
    #     print(f"Task: {task}")
    #     print()

    # print all verina tasks
    # for task in source_meta.keys():
    #     if source_meta[task]['source'] == 'verina':
    #         print(f"Task: {task} id: {source_meta[task]['id']}")

    # # print all clever tasks
    # for task in source_meta.keys():
    #     if source_meta[task]['source'] == 'clever':
    #         print(f"Task: {task} id: {source_meta[task]['id']}")


def generate_ids(source_meta: Dict[str, Any]) -> None:
    """Generate IDs for the files in source_meta.

    For each source, sorts all files and assigns them four-digit zero-padded IDs
    starting from 0000.
    """
    # Group files by source
    files_by_source = {}
    for filename, file_data in source_meta.items():
        source = file_data.get("source")
        if source is None:
            raise ValueError(f"Source is None for {filename}")
        if source not in files_by_source:
            files_by_source[source] = []
        files_by_source[source].append(filename)

    # Sort files within each source and assign IDs
    for source, filenames in files_by_source.items():
        # Sort filenames alphabetically
        sorted_filenames = natsorted(filenames)

        # Assign four-digit zero-padded IDs starting from 0000
        for i, filename in enumerate(sorted_filenames):
            file_id = f"{i:04d}"  # Four-digit zero-padded string
            source_meta[filename]["id"] = file_id

    return source_meta


def generate_metadata(benchmarks_dir: Path) -> None:
    """Generate metadata from benchmarks directory.

    This function runs the main logic from all_generate_metadata.py.

    Args:
        benchmarks_dir: Path to the benchmarks directory
    """
    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")

    # Get source metadata
    source_meta = get_source_meta(benchmarks_dir, save_path=source_meta_default_path)

    # Validate that all entries for each source have consistent signatures
    # validate_source_signatures(source_meta)

    # Print summary counts
    print_summary_counts(source_meta)


def main():
    parser = argparse.ArgumentParser(
        description="Convert YAML spec to target file format"
    )
    parser.add_argument(
        "yaml_file", type=Path, nargs="?", help="Input YAML file or directory"
    )
    parser.add_argument(
        "--suffix",
        choices=["dfy", "lean", "rs", "json", "jsonl"],
        help="Output file suffix",
    )
    parser.add_argument(
        "--dir",
        action="store_true",
        help="Convert all YAML files in directory to a new directory (not available for jsonl)",
    )
    parser.add_argument(
        "--clear-impl",
        action="store_true",
        help="Clear vc-implementation, vc-proof, and vc-code fields with empty strings",
    )
    parser.add_argument(
        "--benchmarks",
        type=Path,
        metavar="BENCHMARKS_DIR",
        help="Process benchmark directories. For each level-2 subfolder benchmarks/XXX/YYY, "
        "convert YAML files in yaml/ folder to files/ folder and create JSONL file",
    )
    parser.add_argument(
        "--all-poor",
        type=Path,
        metavar="BENCHMARKS_DIR",
        help="Process benchmark directories for POOR files. For each level-2 subfolder benchmarks/XXX/YYY, "
        "convert POOR files in poor/ folder to issues/ folder and create JSONL file",
    )
    parser.add_argument(
        "--bench",
        type=Path,
        metavar="BENCH_DIR",
        help="Process a single benchmark directory. Takes a benchmark directory (should contain a yaml subdirectory). Suffix is auto-detected from parent directory if not provided via --suffix",
    )
    parser.add_argument(
        "--poor",
        type=Path,
        metavar="POOR_DIR",
        help="Process a single benchmark directory for POOR files. Takes a benchmark directory (should contain a poor subdirectory). Suffix is auto-detected from parent directory if not provided via --suffix",
    )
    parser.add_argument(
        "--add-postamble",
        action="store_true",
        help="Include vc-postamble in the template output (default: omit for Lean, include for others)",
    )
    parser.add_argument(
        "--metadata",
        type=Path,
        metavar="BENCHMARKS_DIR",
        help="Generate metadata from benchmarks directory. Creates task ids and summarizes task counts.",
    )
    parser.add_argument(
        "--source",
        type=str,
        help="Source identifier for JSONL conversion (used when suffix is jsonl)",
    )
    parser.add_argument(
        "--language",
        type=str,
        help="Language identifier for JSONL conversion (used when suffix is jsonl)",
    )
    parser.add_argument(
        "--source-meta",
        type=Path,
        help="Path to source metadata file for JSONL conversion (used when suffix is jsonl)",
    )
    parser.add_argument(
        "--language-tasks",
        type=Path,
        metavar="BENCHMARKS_DIR",
        help="Process language tasks. For each language directory, generate language tasks file from QA files",
    )

    args = parser.parse_args()

    # Handle metadata generation
    if args.metadata is not None:
        generate_metadata(args.metadata)
        return

    # Handle language tasks processing
    if args.language_tasks is not None:
        process_language_tasks(args.language_tasks)
        return

    # Handle benchmarks processing
    if args.benchmarks is not None:
        process_benchmarks(args.benchmarks, args.suffix, args.add_postamble)
        return

    # Handle all-poor processing
    if args.all_poor is not None:
        process_all_poor(args.all_poor, args.suffix, args.add_postamble)
        return

    # Handle single benchmark processing
    if args.bench is not None:
        process_bench(args.bench, args.suffix, args.add_postamble)
        return

    # Handle single POOR benchmark processing
    if args.poor is not None:
        process_poor(args.poor, args.suffix, args.add_postamble)
        return

    # For non-benchmarks processing, yaml_file is required
    if args.yaml_file is None:
        parser.error(
            "yaml_file is required when not using --benchmarks, --all-poor, --bench, or --poor"
        )

    if not args.yaml_file.exists():
        raise FileNotFoundError(f"{args.yaml_file} does not exist")

    # Handle clear implementation fields option
    if args.clear_impl:
        if args.yaml_file.is_file():
            clear_implementation(args.yaml_file)
        elif args.yaml_file.is_dir():
            # Process all YAML files in directory
            yaml_files = list(args.yaml_file.glob("*.yaml"))
            if not yaml_files:
                print(f"No .yaml files found in {args.yaml_file}")
                return
            for yaml_file in yaml_files:
                clear_implementation(yaml_file)
            print(f"Cleared implementation fields in {len(yaml_files)} YAML files")
        return

    # Original conversion logic
    if not args.suffix:
        parser.error("--suffix is required when not using --clear-impl")

    if args.dir:
        if args.suffix == "jsonl":
            print(
                "Error: --dir option is not available for jsonl suffix (use without --dir for JSONL)"
            )
            return
        convert_yaml_to_dir(
            args.suffix, args.yaml_file, add_postamble=args.add_postamble
        )
    elif args.suffix == "json":
        output_path = args.yaml_file.with_suffix(f".{args.suffix}")
        convert_yaml_to_json(args.yaml_file, output_path)
    elif args.suffix == "jsonl":
        convert_yaml_to_jsonl(
            args.yaml_file,
            source=args.source,
            language=args.language,
            source_meta_path=args.source_meta,
        )
    else:
        output_path = args.yaml_file.with_suffix(f".{args.suffix}")
        convert_yaml_to_file(args.yaml_file, output_path, args.add_postamble)


if __name__ == "__main__":
    main()
