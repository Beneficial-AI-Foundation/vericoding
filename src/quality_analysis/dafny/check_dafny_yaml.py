#!/usr/bin/env python3
"""
Script to analyze Dafny YAML files and detect implementation quality issues.

This script uses YAML parsing for more reliable analysis of Dafny verification code.
It focuses on YAML files with embedded Dafny code rather than raw .dfy files.

Categories analyzed:
1. 🚀 Proper specification: Functions/predicates with meaningful logical content
2. ⚠️  Default value: Functions/predicates returning simple default values (0, false, empty collections)
3. 🔄 Placeholder: Functions/predicates that are empty or incomplete
4. 📝 Methods with implementations: Methods that have actual code instead of assume {:axiom} false
5. ✅ Methods with assume false: Methods using the expected assume {:axiom} false pattern

This script:
1. Finds all .yaml files in the specified directory
2. Extracts functions/predicates from vc-preamble sections using YAML parsing
3. Extracts methods from vc-code sections using YAML parsing
4. Categorizes each by implementation quality
5. Generates detailed statistics and file lists

Usage:
    python3 check_dafny_yaml.py                        # Full analysis with statistics
    python3 check_dafny_yaml.py --list-implementations # Only list files with method implementations
    python3 check_dafny_yaml.py --list-defaults        # Only list files with default-value functions
    python3 check_dafny_yaml.py --help                 # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- dafny_yaml_functions_with_defaults.txt: Files containing functions with default values
- dafny_yaml_methods_with_implementations.txt: Files with methods having actual implementations
- dafny_yaml_proper_specifications.txt: Files with meaningful function implementations
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
    # Use a simple approach - find function/predicate start, then use brace counting
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


def extract_method_from_code(yaml_content: Dict) -> Tuple[str, str, int]:
    """
    Extract method body from vc-code section.
    Returns tuple: (method_name, body, line_number) or ("unknown", "", 0) if not found
    """
    # Get vc-code content
    vc_code = yaml_content.get("vc-code", "").strip()
    if not vc_code:
        return ("unknown", "", 0)

    # Remove the outer braces if present
    if vc_code.startswith("{") and vc_code.endswith("}"):
        body = vc_code[1:-1].strip()
    else:
        body = vc_code

    # Try to find method name from vc-spec section
    method_name = "unknown_method"
    vc_spec = yaml_content.get("vc-spec", "")
    if vc_spec:
        spec_match = re.search(r"method\s+(\w+)\s*\(", vc_spec)
        if spec_match:
            method_name = spec_match.group(1)

    return (method_name, body, 1)


def is_assume_false(body: str) -> bool:
    """
    Check if a method body uses the expected assume {:axiom} false pattern.
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"//.*$", "", body, flags=re.MULTILINE)  # Remove line comments
    normalized = re.sub(
        r"/\*.*?\*/", "", normalized, flags=re.DOTALL
    )  # Remove block comments
    normalized = re.sub(r"\s+", " ", normalized).strip()  # Normalize whitespace

    # Check for assume {:axiom} false pattern (with variations)
    assume_patterns = [
        r"assume\s*\{:\s*axiom\s*\}\s*false\s*;?",
        r"assume\s*false\s*;?",  # Simple assume false
        r"assume\s*\{:axiom\}\s*false\s*;?",  # Without spaces
    ]

    for pattern in assume_patterns:
        if re.search(pattern, normalized, re.IGNORECASE):
            return True

    return False


def is_default_value(body: str, func_type: str = "") -> bool:
    """
    Check if a function/predicate body represents a default value.
    Only return True for very simple, obvious default values.
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"//.*$", "", body, flags=re.MULTILINE)
    normalized = re.sub(r"/\*.*?\*/", "", normalized, flags=re.DOTALL)
    normalized = re.sub(r"\s+", " ", normalized).strip()

    # Only flag very simple, obvious default values
    # Exclude anything with control flow (if/match), function calls, or complex logic
    if len(normalized.split()) > 3:  # More than 3 words is likely not a simple default
        return False

    if any(
        keyword in normalized.lower()
        for keyword in ["if", "match", "case", "then", "else", "while", "for"]
    ):
        return False

    if "(" in normalized:  # Function calls are not simple defaults
        return False

    # Very simple default value patterns for Dafny
    default_patterns = [
        # Numeric defaults (standalone)
        r"^0$",
        r"^0\.0$",
        r"^1$",
        r"^-1$",
        # Boolean defaults (standalone)
        r"^true$",
        r"^false$",
        # String defaults (standalone)
        r'^""$',
        r"^''$",
        # Collection defaults (standalone)
        r"^\[\]$",
        r"^\{\}$",
        r"^set\s*\{\}$",
        r"^seq\s*\[\]$",
        r"^multiset\s*\{\}$",
        r"^map\s*\[\]$",
    ]

    for pattern in default_patterns:
        if re.match(pattern, normalized):
            return True

    return False


def is_placeholder(body: str) -> bool:
    """
    Check if a function/predicate body uses placeholders or is incomplete.
    """
    normalized = body.strip()

    # Empty or very short bodies
    if len(normalized) == 0 or len(normalized.split()) <= 2:
        return True

    # Placeholder patterns
    placeholder_patterns = [
        r"assume\s*false",
        r"todo",
        r"unimplemented",
        r"undefined",
        r"\?\?\?",
    ]

    for pattern in placeholder_patterns:
        if re.search(pattern, normalized, re.IGNORECASE):
            return True

    return False


def analyze_method_body(body: str) -> Tuple[str, bool]:
    """
    Analyze method body and return (category, is_problematic).

    Categories:
    - "assume_false": Uses the expected assume {:axiom} false pattern
    - "has_implementation": Has actual implementation code

    Returns:
        tuple: (category, is_problematic)
    """
    if is_assume_false(body):
        return ("assume_false", False)
    else:
        return ("has_implementation", True)


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
    Check a single Dafny YAML file and analyze all functions/methods.

    Returns:
        tuple: (problematic_items, item_categories)
        - problematic_items: List of (name, line_number, body, category, type)
        - item_categories: Dict with counts for each category
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

    # Extract method from vc-code
    method_name, method_body, method_line = extract_method_from_code(yaml_content)

    problematic = []
    categories = {
        # Method categories
        "assume_false": 0,
        "has_implementation": 0,
        # Function/predicate categories
        "proper_specification": 0,
        "default_value": 0,
        "placeholder": 0,
    }

    # Analyze method (if present)
    if method_body:
        category, is_problematic = analyze_method_body(method_body)
        categories[category] += 1

        if is_problematic:
            problematic.append(
                (method_name, method_line, method_body, category, "method")
            )

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
        description="Analyze Dafny YAML files and detect implementation quality issues",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_dafny_yaml.py                          # Full analysis with statistics (default directory)
  python3 check_dafny_yaml.py /path/to/file.yaml       # Analyze single YAML file
  python3 check_dafny_yaml.py /path/to/directory       # Analyze directory
  python3 check_dafny_yaml.py --list-implementations   # Only list files with method implementations  
  python3 check_dafny_yaml.py --list-defaults          # Only list files with default-value functions
  python3 check_dafny_yaml.py file.yaml --list-defaults # List defaults for single file
  python3 check_dafny_yaml.py --include-problematic    # Include 'poor'/'problematic' dirs
        """,
    )
    parser.add_argument(
        "--list-implementations",
        action="store_true",
        help="Only list files with methods having actual implementations (no statistics)",
    )
    parser.add_argument(
        "--list-defaults",
        action="store_true",
        help="Only list files with functions/predicates returning default values (no statistics)",
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-* options)",
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
    files_with_implementations = []
    files_with_defaults = []
    files_with_placeholders = []
    files_with_proper_specs = []

    total_categories = {
        "assume_false": 0,
        "has_implementation": 0,
        "proper_specification": 0,
        "default_value": 0,
        "placeholder": 0,
    }

    total_items = 0
    total_problematic_items = 0

    # Check each file
    for file_path in yaml_files:
        problematic_items, categories = check_dafny_yaml_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_items += sum(categories.values())

        if problematic_items:
            total_problematic_items += len(problematic_items)

        # Track files by category
        if categories.get("has_implementation", 0) > 0:
            files_with_implementations.append(str(file_path))

        if categories.get("default_value", 0) > 0:
            files_with_defaults.append(str(file_path))

        if categories.get("placeholder", 0) > 0:
            files_with_placeholders.append(str(file_path))

        if categories.get("proper_specification", 0) > 0:
            files_with_proper_specs.append(str(file_path))

    # Handle --list-* options
    if args.list_implementations:
        if not args.quiet:
            print(
                f"\nFiles with methods having actual implementations ({len(files_with_implementations)} files):"
            )
            print("=" * 60)

        for file_path in files_with_implementations:
            print(file_path)

        if not args.quiet:
            print(
                f"\nTotal: {len(files_with_implementations)} files with method implementations"
            )

        return {
            "files_with_implementations": files_with_implementations,
            "count": len(files_with_implementations),
        }

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
        print(f"Total methods/functions/predicates found: {total_items}")
        print()
        print("Method Analysis:")
        print(f"  ✅ Using assume false (expected): {total_categories['assume_false']}")
        print(
            f"  📝 Has actual implementation: {total_categories['has_implementation']}"
        )
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
        if total_items > 0:
            print(
                f"  Files with proper function specs: {len(files_with_proper_specs)} ({100 * len(files_with_proper_specs) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with method implementations: {len(files_with_implementations)} ({100 * len(files_with_implementations) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with default-value functions: {len(files_with_defaults)} ({100 * len(files_with_defaults) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with placeholder functions: {len(files_with_placeholders)} ({100 * len(files_with_placeholders) / len(yaml_files):.1f}%)"
            )
        else:
            print("  No methods/functions/predicates found")

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if files_with_implementations:
            with open("dafny_yaml_methods_with_implementations.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with methods having actual implementations:\n"
                )
                f.write(
                    "# These methods should typically use 'assume {:axiom} false;' as placeholders\n\n"
                )
                for file_path in files_with_implementations:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(files_with_implementations)} files with method implementations to: dafny_yaml_methods_with_implementations.txt"
            )

        if files_with_defaults:
            with open("dafny_yaml_functions_with_defaults.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with functions/predicates returning default values:\n"
                )
                f.write(
                    "# These should provide meaningful logical specifications instead of simple defaults\n\n"
                )
                for file_path in files_with_defaults:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_defaults)} files with default-value functions to: dafny_yaml_functions_with_defaults.txt"
            )

        if files_with_proper_specs:
            with open("dafny_yaml_proper_specifications.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with proper function/predicate implementations:\n"
                )
                f.write("# These files contain meaningful logical specifications\n\n")
                for file_path in files_with_proper_specs:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_proper_specs)} files with proper specs to: dafny_yaml_proper_specifications.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if files_with_implementations:
            print("\nFirst 10 files with method implementations:")
            for file_path in files_with_implementations[:10]:
                print(f"  {file_path}")
            if len(files_with_implementations) > 10:
                print(f"  ... and {len(files_with_implementations) - 10} more")

        if files_with_defaults:
            print("\nFirst 10 files with default-value functions:")
            for file_path in files_with_defaults[:10]:
                print(f"  {file_path}")
            if len(files_with_defaults) > 10:
                print(f"  ... and {len(files_with_defaults) - 10} more")

    return {
        "files_with_implementations": files_with_implementations,
        "files_with_defaults": files_with_defaults,
        "files_with_placeholders": files_with_placeholders,
        "files_with_proper_specs": files_with_proper_specs,
        "statistics": total_categories,
    }


if __name__ == "__main__":
    result = main()
