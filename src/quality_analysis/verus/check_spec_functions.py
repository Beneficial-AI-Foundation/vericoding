#!/usr/bin/env python3
"""
Script to analyze Verus spec functions and detect those with default values.

This script analyzes YAML files with embedded Verus code, which is much more reliable than
parsing raw Verus source files. It looks specifically at vc-preamble sections for spec functions
that return default values instead of proper specifications.

Categories analyzed:
1. 🚀 Proper specification: Spec functions with meaningful logical content
2. ⚠️  Default value: Spec functions returning simple default values (0, false, empty collections)
3. 🔄 Placeholder: Spec functions using arbitrary() or similar placeholders

This script:
1. Finds all .yaml files in the specified directory
2. Extracts spec functions from vc-preamble sections using YAML parsing
3. Categorizes each spec function by implementation quality
4. Generates detailed statistics and file lists

Usage:
    python3 check_spec_functions.py                           # Full analysis with statistics (default directory)
    python3 check_spec_functions.py /path/to/file.yaml        # Analyze single YAML file
    python3 check_spec_functions.py /path/to/directory        # Analyze directory
    python3 check_spec_functions.py --list-defaults           # Only list files with default-value specs
    python3 check_spec_functions.py file.yaml --list-defaults # List defaults for single file
    python3 check_spec_functions.py --help                    # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- verus_yaml_spec_functions_with_defaults.txt: Files with default-value spec functions
- verus_yaml_spec_functions_with_placeholders.txt: Files with placeholder spec functions
- verus_yaml_proper_spec_functions.txt: Files with meaningful spec functions
"""

import os
import re
import argparse
import yaml
from pathlib import Path
from typing import List, Tuple, Dict


def find_verus_yaml_files(
    directory: str, exclude_problematic: bool = True
) -> List[Path]:
    """Find all .yaml files in the given directory and subdirectories.

    Args:
        directory: Root directory to search
        exclude_problematic: If True, exclude files in directories with problematic names
    """
    yaml_files = []

    # Directory names that indicate problematic/failed implementations or duplicates
    problematic_dirs = {
        "poor",
        "non_compiling",
        "failing",
        "broken",
        "error",
        "failed",
        "incomplete",
        "partial",
        "temp",
        "temporary",
        "test_failures",
        "bad",
        "invalid",
        "wrong",
        "files_mine",
        "apps_2",
        "bignum_2",
    }

    for root, dirs, files in os.walk(directory):
        # Check if current path contains any problematic directory names
        if exclude_problematic:
            path_parts = Path(root).parts
            if any(part.lower() in problematic_dirs for part in path_parts):
                continue  # Skip this directory

        for file in files:
            if file.endswith(".yaml"):
                yaml_files.append(Path(root) / file)

    return yaml_files


def extract_spec_functions_from_yaml(yaml_content: Dict) -> List[Tuple[str, str, int]]:
    """
    Extract spec function names and their bodies from vc-preamble section.
    Returns list of tuples: (function_name, body, line_number)
    """
    spec_functions = []

    # Get vc-preamble content
    vc_preamble = yaml_content.get("vc-preamble", "")
    if not vc_preamble:
        return spec_functions

    # Pattern to match spec functions with their bodies - much simpler for single-line functions
    spec_fn_pattern = (
        r"spec\s+fn\s+(\w+)\s*\([^)]*\)(?:\s*->\s*[^{]+)?\s*\{\s*([^}]*)\s*\}"
    )

    matches = re.finditer(spec_fn_pattern, vc_preamble, re.MULTILINE)

    for match in matches:
        fn_name = match.group(1)
        body = match.group(2).strip()
        # Calculate line number within the vc-preamble
        line_number = vc_preamble[: match.start()].count("\n") + 1
        spec_functions.append((fn_name, body, line_number))

    return spec_functions


def is_default_value(body: str) -> bool:
    """
    Check if a spec function body represents a default value.
    """
    # Normalize whitespace
    normalized = body.strip()

    # Common default value patterns for Verus
    default_patterns = [
        # Numeric defaults
        r"^0$",
        r"^0\.0$",
        r"^1$",
        r"^-1$",
        # Boolean defaults
        r"^true$",
        r"^false$",
        # String defaults
        r'^""$',
        r"^''$",
        # Collection defaults - Verus specific
        r"^seq!\[\]$",
        r"^Seq::empty\(\)$",
        r"^Vec::new\(\)$",
        r"^vec!\[\]$",
        r"^\[\]$",
        r"^\{\}$",
        r"^None$",
        # Simple conditionals that return defaults
        r"^if\s+.+\s*\{\s*0\s*\}\s*else\s*\{\s*0\s*\}$",
        r"^if\s+.+\s*\{\s*false\s*\}\s*else\s*\{\s*false\s*\}$",
    ]

    for pattern in default_patterns:
        if re.match(pattern, normalized):
            return True

    return False


def is_placeholder(body: str) -> bool:
    """
    Check if a spec function body uses placeholders like arbitrary().
    """
    normalized = body.strip()

    # Placeholder patterns specific to Verus
    placeholder_patterns = [
        r"arbitrary\(\)",
        r"unimplemented!\(\)",
        r"todo!\(\)",
        r"unreached\(\)",
        r"panic!\(",
        r"assume\s*\(",
    ]

    for pattern in placeholder_patterns:
        if re.search(pattern, normalized):
            return True

    return False


def analyze_spec_function_body(body: str) -> Tuple[str, bool]:
    """
    Analyze spec function body and return (category, is_problematic).

    Categories:
    - "proper_specification": Has meaningful logical content
    - "default_value": Returns simple default values
    - "placeholder": Uses arbitrary() or similar placeholders

    Returns:
        tuple: (category, is_problematic)
    """
    if is_placeholder(body):
        return ("placeholder", True)
    elif is_default_value(body):
        return ("default_value", True)
    else:
        return ("proper_specification", False)


def check_verus_yaml_file(file_path: Path) -> Tuple[List, Dict]:
    """
    Check a single Verus YAML file and analyze all spec functions in vc-preamble.

    Returns:
        tuple: (problematic_functions, function_categories)
        - problematic_functions: List of (function_name, line_number, body, category)
        - function_categories: Dict with counts for each category
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            yaml_content = yaml.safe_load(f)
    except Exception as e:
        print(f"Warning: Could not parse YAML {file_path}: {e}")
        return [], {}

    if not yaml_content:
        return [], {}

    spec_functions = extract_spec_functions_from_yaml(yaml_content)
    problematic = []
    categories = {"proper_specification": 0, "default_value": 0, "placeholder": 0}

    for fn_name, body, line_number in spec_functions:
        category, is_problematic = analyze_spec_function_body(body)
        categories[category] += 1

        if is_problematic:
            problematic.append((fn_name, line_number, body, category))

    return problematic, categories


def main():
    """Main function to check all Verus YAML files."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Verus YAML files and detect spec functions with default values",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_spec_functions.py                           # Full analysis with statistics (default directory)
  python3 check_spec_functions.py /path/to/file.yaml        # Analyze single YAML file
  python3 check_spec_functions.py /path/to/directory        # Analyze directory
  python3 check_spec_functions.py --list-defaults           # Only list files with default-value specs
  python3 check_spec_functions.py file.yaml --list-defaults # List defaults for single file
  python3 check_spec_functions.py --include-problematic     # Include 'poor'/'non_compiling' dirs
        """,
    )
    parser.add_argument(
        "--list-defaults",
        action="store_true",
        help="Only list files with spec functions returning default values (no statistics)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-defaults)",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default="/home/lacra/git_repos/baif/vericoding/benchmarks/verus",
        help="YAML file or directory to check (default: %(default)s)",
    )
    parser.add_argument(
        "--dir",
        help="Directory to check (deprecated: use positional path argument instead)",
    )
    parser.add_argument(
        "--include-problematic",
        action="store_true",
        help="Include files in 'poor', 'non_compiling', etc. directories (default: exclude them)",
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )

    args = parser.parse_args()

    # Handle path argument (support for backward compatibility with --dir)
    if args.dir:
        check_path = args.dir
    else:
        check_path = args.path

    if not os.path.exists(check_path):
        print(f"Error: Path {check_path} does not exist")
        return

    # Determine if we're checking a single file or directory
    is_single_file = os.path.isfile(check_path)

    if is_single_file:
        # Single file mode
        if not check_path.endswith(".yaml"):
            print(f"Error: {check_path} is not a YAML file")
            return

        yaml_files = [Path(check_path)]
        if not args.quiet:
            print(f"Checking single Verus YAML file: {check_path}")
            print("=" * 60)
    else:
        # Directory mode
        if not args.quiet:
            print(f"Checking Verus YAML files in: {check_path}")
            print("=" * 60)

        # Find all YAML files
        exclude_problematic = not args.include_problematic
        yaml_files = find_verus_yaml_files(
            check_path, exclude_problematic=exclude_problematic
        )
        if not args.quiet:
            excluded_note = (
                " (excluding problematic directories)"
                if exclude_problematic
                else " (including all directories)"
            )
            print(f"Found {len(yaml_files)} YAML files{excluded_note}")

    # Track statistics
    files_with_defaults = []
    files_with_placeholders = []
    files_with_proper_specs = []

    total_categories = {"proper_specification": 0, "default_value": 0, "placeholder": 0}

    total_spec_functions = 0
    total_problematic_functions = 0

    # Check each file
    for file_path in yaml_files:
        problematic_functions, categories = check_verus_yaml_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_spec_functions += sum(categories.values())

        if problematic_functions:
            total_problematic_functions += len(problematic_functions)

        # Track files by category
        if categories.get("default_value", 0) > 0:
            files_with_defaults.append(str(file_path))

        if categories.get("placeholder", 0) > 0:
            files_with_placeholders.append(str(file_path))

        if categories.get("proper_specification", 0) > 0:
            files_with_proper_specs.append(str(file_path))

    # Handle --list-defaults option
    if args.list_defaults:
        if not args.quiet:
            print(
                f"\nFiles with spec functions returning default values ({len(files_with_defaults)} files):"
            )
            print("=" * 60)

        for file_path in files_with_defaults:
            print(file_path)

        if not args.quiet:
            print(
                f"\nTotal: {len(files_with_defaults)} files with default-value spec functions"
            )

        result = {
            "files_with_defaults": files_with_defaults,
            "count": len(files_with_defaults),
        }

        # Handle JSON output
        if args.output == "json":
            import json

            print(json.dumps(result, indent=2))

        return result

    # Full analysis mode - Summary
    if not args.quiet:
        print("\n" + "=" * 60)
        print("SUMMARY:")
        print(f"Total YAML files checked: {len(yaml_files)}")
        print(f"Total spec functions found: {total_spec_functions}")
        print()
        print("Spec Function Analysis:")
        print(
            f"  🚀 Proper specification (meaningful logic): {total_categories['proper_specification']}"
        )
        print(
            f"  ⚠️  Default value (0, false, empty, etc.): {total_categories['default_value']}"
        )
        print(
            f"  🔄 Placeholder (arbitrary, unimplemented): {total_categories['placeholder']}"
        )
        print()
        print("File Statistics:")
        if total_spec_functions > 0:
            print(
                f"  Files with proper specs: {len(files_with_proper_specs)} ({100 * len(files_with_proper_specs) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with default-value specs: {len(files_with_defaults)} ({100 * len(files_with_defaults) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with placeholder specs: {len(files_with_placeholders)} ({100 * len(files_with_placeholders) / len(yaml_files):.1f}%)"
            )
        else:
            print("  No spec functions found in vc-preamble sections")

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if files_with_defaults:
            with open("verus_yaml_spec_functions_with_defaults.txt", "w") as f:
                f.write(
                    "# Verus YAML files with spec functions returning default values:\n"
                )
                f.write(
                    "# These spec functions should provide meaningful logical specifications\n"
                )
                f.write(
                    "# instead of simple default values like 0, false, seq![], etc.\n\n"
                )
                for file_path in files_with_defaults:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(files_with_defaults)} files with default-value specs to: verus_yaml_spec_functions_with_defaults.txt"
            )

        if files_with_placeholders:
            with open("verus_yaml_spec_functions_with_placeholders.txt", "w") as f:
                f.write("# Verus YAML files with spec functions using placeholders:\n")
                f.write(
                    "# These spec functions use arbitrary(), unimplemented!(), etc.\n\n"
                )
                for file_path in files_with_placeholders:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_placeholders)} files with placeholder specs to: verus_yaml_spec_functions_with_placeholders.txt"
            )

        if files_with_proper_specs:
            with open("verus_yaml_proper_spec_functions.txt", "w") as f:
                f.write(
                    "# Verus YAML files with proper spec function implementations:\n"
                )
                f.write("# These files contain meaningful logical specifications\n\n")
                for file_path in files_with_proper_specs:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_proper_specs)} files with proper specs to: verus_yaml_proper_spec_functions.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if files_with_defaults:
            print("\nFirst 10 files with default-value spec functions:")
            for file_path in files_with_defaults[:10]:
                print(f"  {file_path}")
            if len(files_with_defaults) > 10:
                print(f"  ... and {len(files_with_defaults) - 10} more")

        if files_with_placeholders:
            print("\nFirst 10 files with placeholder spec functions:")
            for file_path in files_with_placeholders[:10]:
                print(f"  {file_path}")
            if len(files_with_placeholders) > 10:
                print(f"  ... and {len(files_with_placeholders) - 10} more")

    result = {
        "files_with_defaults": files_with_defaults,
        "files_with_placeholders": files_with_placeholders,
        "files_with_proper_specs": files_with_proper_specs,
        "statistics": total_categories,
    }

    # Handle JSON output
    if args.output == "json":
        import json

        print(json.dumps(result, indent=2))

    return result


if __name__ == "__main__":
    result = main()
