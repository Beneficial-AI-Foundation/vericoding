#!/usr/bin/env python3
"""
Script to analyze Dafny functions and predicates in YAML files for default values.

This script focuses specifically on functions and predicates in vc-preamble sections,
checking for those that return simple default values instead of meaningful specifications.

Categories analyzed:
1. 🚀 Proper specification: Functions/predicates with meaningful logical content
2. ⚠️  Default value: Functions/predicates returning simple default values (0, false, empty collections)
3. 🔄 Placeholder: Functions/predicates that are empty or incomplete

This script:
1. Finds all .yaml files in the specified directory
2. Extracts functions/predicates from vc-preamble sections using YAML parsing
3. Categorizes each by implementation quality
4. Generates detailed statistics and file lists

Usage:
    python3 check_dafny_functions.py                        # Full analysis with statistics
    python3 check_dafny_functions.py --list-defaults        # Only list files with default-value functions
    python3 check_dafny_functions.py --list-defaults --quiet # List defaults without headers
    python3 check_dafny_functions.py --help                 # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- dafny_functions_with_defaults.txt: Files containing functions with default values
- dafny_functions_with_placeholders.txt: Files with placeholder functions
- dafny_proper_specifications.txt: Files with meaningful function implementations
"""

import os
import re
import argparse
import yaml
from pathlib import Path
from typing import List, Tuple, Dict


def find_dafny_yaml_files(
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
        "problematic",
        "default_values",  # Dafny-specific problematic dirs
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


def extract_functions_from_preamble(
    yaml_content: Dict,
) -> List[Tuple[str, str, str, int]]:
    """
    Extract function/predicate names and their bodies from vc-preamble section.
    Returns list of tuples: (name, body, type, line_number)
    """
    functions = []

    # Get vc-preamble content
    vc_preamble = yaml_content.get("vc-preamble", "")
    if not vc_preamble:
        return functions

    # Patterns to match functions and predicates with their bodies
    patterns = [
        (r"function\s+(\w+)\s*\([^)]*\)(?:\s*:\s*[^{]+)?\s*\{", "function"),
        (r"predicate\s+(\w+)\s*\([^)]*\)(?:\s*:\s*[^{]+)?\s*\{", "predicate"),
    ]

    for pattern, func_type in patterns:
        matches = re.finditer(pattern, vc_preamble, re.MULTILINE | re.DOTALL)

        for match in matches:
            fn_name = match.group(1)

            # Extract body using brace counting
            start_pos = match.end()  # Position after the opening {
            brace_count = 1
            pos = start_pos

            while pos < len(vc_preamble) and brace_count > 0:
                if vc_preamble[pos] == "{":
                    brace_count += 1
                elif vc_preamble[pos] == "}":
                    brace_count -= 1
                pos += 1

            if brace_count == 0:
                # Extract body content (excluding the final })
                body = vc_preamble[start_pos : pos - 1].strip()
            else:
                # Fallback - couldn't find matching brace
                body = ""

            # Calculate line number within the vc-preamble
            line_number = vc_preamble[: match.start()].count("\n") + 1
            functions.append((fn_name, body, func_type, line_number))

    return functions


def is_default_value(body: str, func_type: str = "") -> bool:
    """
    Check if a function/predicate body represents a default value.
    Similar logic to Verus script for fair comparison.
    """
    # Normalize whitespace
    normalized = body.strip()

    # Common default value patterns for Dafny (similar to Verus patterns)
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
        r'^"0"$',
        r"^'0'$",
        # Collection defaults - Dafny specific
        r"^\[\]$",
        r"^\{\}$",
        r"^set\s*\{\}$",
        r"^seq\s*\[\]$",
        r"^multiset\s*\{\}$",
        r"^map\s*\[\]$",
        # Simple tuples with default values
        r"^\(\s*\d+\s*,\s*\d+\s*\)$",  # (2, 2) etc.
        r"^\(\s*\d+\s*,\s*\d+\s*,\s*\[\[.*\]\]\s*\)$",  # (2, 2, [[0, 0], [0, 0]])
        # Simple lists with default values
        r'^\[\s*"[^"]*"\s*\]$',  # ["0"] etc.
        r"^\[\s*\[.*\]\s*\]$",  # [[0, 0], [0, 0]] etc.
        # Simple conditionals that return defaults (like Verus)
        r"^if\s+.+\s*then\s*\d+\s*else\s*\d+$",
        r"^if\s+.+\s*then\s*(true|false)\s*else\s*(true|false)$",
    ]

    for pattern in default_patterns:
        if re.match(pattern, normalized):
            return True

    return False


def is_placeholder(body: str) -> bool:
    """
    Check if a function/predicate body uses placeholders.
    Similar logic to Verus script for fair comparison.
    """
    normalized = body.strip()

    # Placeholder patterns similar to Verus script
    placeholder_patterns = [
        r"assume\s*false",
        r"assume\s*\(",
        r"todo",
        r"unimplemented",
        r"undefined",
        r"\?\?\?",
    ]

    for pattern in placeholder_patterns:
        if re.search(pattern, normalized, re.IGNORECASE):
            return True

    return False


def analyze_function_body(body: str, func_type: str = "") -> Tuple[str, bool]:
    """
    Analyze function/predicate body and return (category, is_problematic).

    Categories:
    - "proper_specification": Has meaningful logical content
    - "default_value": Returns simple default values
    - "placeholder": Empty or incomplete

    Returns:
        tuple: (category, is_problematic)
    """
    if is_placeholder(body):
        return ("placeholder", True)
    elif is_default_value(body, func_type):
        return ("default_value", True)
    else:
        return ("proper_specification", False)


def check_dafny_yaml_file(file_path: Path) -> Tuple[List, Dict]:
    """
    Check a single Dafny YAML file and analyze all functions/predicates.

    Returns:
        tuple: (problematic_functions, function_categories)
        - problematic_functions: List of (name, line_number, body, category, type)
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

    # Extract functions/predicates from vc-preamble
    functions = extract_functions_from_preamble(yaml_content)

    problematic = []
    categories = {"proper_specification": 0, "default_value": 0, "placeholder": 0}

    # Analyze functions/predicates
    for name, body, func_type, line_number in functions:
        category, is_problematic = analyze_function_body(body, func_type)
        categories[category] += 1

        if is_problematic:
            problematic.append((name, line_number, body, category, func_type))

    return problematic, categories


def main():
    """Main function to check all Dafny YAML files."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Dafny functions and predicates in YAML files for default values",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_dafny_functions.py                         # Full analysis with statistics (default directory)
  python3 check_dafny_functions.py /path/to/file.yaml      # Analyze single YAML file
  python3 check_dafny_functions.py /path/to/directory      # Analyze directory
  python3 check_dafny_functions.py --list-defaults         # Only list files with default-value functions
  python3 check_dafny_functions.py file.yaml --list-defaults # List defaults for single file
  python3 check_dafny_functions.py --include-problematic   # Include 'poor'/'problematic' dirs
        """,
    )
    parser.add_argument(
        "--list-defaults",
        action="store_true",
        help="Only list files with functions/predicates returning default values (no statistics)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-defaults)",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default="benchmarks/dafny",
        help="YAML file or directory to check (default: %(default)s)",
    )
    parser.add_argument(
        "--dir",
        help="Directory to check (deprecated: use positional path argument instead)",
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--include-problematic",
        action="store_true",
        help="Include files in 'poor', 'problematic', etc. directories (default: exclude them)",
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
            print(f"Checking single Dafny YAML file: {check_path}")
            print("=" * 60)
    else:
        # Directory mode
        if not args.quiet:
            print(f"Checking Dafny YAML files in: {check_path}")
            print("=" * 60)

        # Find all YAML files
        exclude_problematic = not args.include_problematic
        yaml_files = find_dafny_yaml_files(
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

    total_functions = 0
    total_problematic_functions = 0

    # Check each file
    for file_path in yaml_files:
        problematic_functions, categories = check_dafny_yaml_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_functions += sum(categories.values())

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
                f"\nFiles with functions/predicates returning default values ({len(files_with_defaults)} files):"
            )
            print("=" * 60)

        for file_path in files_with_defaults:
            print(file_path)

        if not args.quiet:
            print(
                f"\nTotal: {len(files_with_defaults)} files with default-value functions"
            )

        return {
            "files_with_defaults": files_with_defaults,
            "count": len(files_with_defaults),
        }

    # Full analysis mode - Summary
    if not args.quiet:
        print("\n" + "=" * 60)
        print("SUMMARY:")
        print(f"Total YAML files checked: {len(yaml_files)}")
        print(f"Total functions/predicates found: {total_functions}")
        print()
        print("Function/Predicate Analysis:")
        print(
            f"  🚀 Proper specification (meaningful logic): {total_categories['proper_specification']}"
        )
        print(
            f"  ⚠️  Default value (0, false, empty, etc.): {total_categories['default_value']}"
        )
        print(
            f"  🔄 Placeholder (empty or incomplete): {total_categories['placeholder']}"
        )
        print()
        print("File Statistics:")
        if total_functions > 0:
            print(
                f"  Files with proper function specs: {len(files_with_proper_specs)} ({100 * len(files_with_proper_specs) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with default-value functions: {len(files_with_defaults)} ({100 * len(files_with_defaults) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with placeholder functions: {len(files_with_placeholders)} ({100 * len(files_with_placeholders) / len(yaml_files):.1f}%)"
            )
        else:
            print("  No functions/predicates found in vc-preamble sections")

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if files_with_defaults:
            with open("dafny_functions_with_defaults.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with functions/predicates returning default values:\n"
                )
                f.write(
                    "# These should provide meaningful logical specifications instead of simple defaults\n\n"
                )
                for file_path in files_with_defaults:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(files_with_defaults)} files with default-value functions to: dafny_functions_with_defaults.txt"
            )

        if files_with_placeholders:
            with open("dafny_functions_with_placeholders.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with functions/predicates using placeholders:\n"
                )
                f.write(
                    "# These functions/predicates are incomplete or use placeholder logic\n\n"
                )
                for file_path in files_with_placeholders:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_placeholders)} files with placeholder functions to: dafny_functions_with_placeholders.txt"
            )

        if files_with_proper_specs:
            with open("dafny_proper_specifications.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with proper function/predicate implementations:\n"
                )
                f.write("# These files contain meaningful logical specifications\n\n")
                for file_path in files_with_proper_specs:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_proper_specs)} files with proper specs to: dafny_proper_specifications.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if files_with_defaults:
            print("\nFirst 10 files with default-value functions:")
            for file_path in files_with_defaults[:10]:
                print(f"  {file_path}")
            if len(files_with_defaults) > 10:
                print(f"  ... and {len(files_with_defaults) - 10} more")

        if files_with_placeholders:
            print("\nFirst 10 files with placeholder functions:")
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
    
    # Output JSON if requested
    if args.output == "json":
        import json
        print(json.dumps(result, indent=2))
    
    return result


if __name__ == "__main__":
    result = main()
