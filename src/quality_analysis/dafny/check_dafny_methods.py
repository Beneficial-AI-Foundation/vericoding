#!/usr/bin/env python3
"""
Script to analyze Dafny methods in YAML files for implementation quality.

This script focuses specifically on methods in vc-code sections,
checking for those that have actual implementations instead of the expected assume {:axiom} false pattern.

Categories analyzed:
1. ✅ Using assume false (expected): Methods with assume {:axiom} false pattern
2. 📝 Has actual implementation: Methods with real code instead of placeholder

This script:
1. Finds all .yaml files in the specified directory
2. Extracts methods from vc-code sections using YAML parsing
3. Categorizes each by implementation type
4. Generates detailed statistics and file lists

Usage:
    python3 check_dafny_methods.py                        # Full analysis with statistics
    python3 check_dafny_methods.py --list-implementations # Only list files with method implementations
    python3 check_dafny_methods.py --list-implementations --quiet # List implementations without headers
    python3 check_dafny_methods.py --help                 # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- dafny_methods_with_implementations.txt: Files with methods having actual implementations
- dafny_methods_with_assume_false.txt: Files with methods using expected assume false pattern
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


def is_simple_default_return(body: str) -> bool:
    """
    Check if a method body contains only simple default return values.
    These are acceptable placeholder implementations.
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"//.*$", "", body, flags=re.MULTILINE)  # Remove line comments
    normalized = re.sub(r"/\*.*?\*/", "", normalized, flags=re.DOTALL)  # Remove block comments
    normalized = re.sub(r"\s+", " ", normalized).strip()  # Normalize whitespace
    
    # Remove common TODO/placeholder comments
    normalized = re.sub(r"(?i)todo[:\s]*[^;]*", "", normalized)
    normalized = re.sub(r"(?i)impl-start.*?impl-end", "", normalized, flags=re.DOTALL)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    
    # Patterns for simple default return values
    simple_return_patterns = [
        # Simple variable assignments to default values
        r"^result\s*:=\s*0\s*;?$",                    # result := 0;
        r"^result\s*:=\s*false\s*;?$",               # result := false;
        r"^result\s*:=\s*true\s*;?$",                # result := true;
        r'^result\s*:=\s*""\s*;?$',                  # result := "";
        r"^result\s*:=\s*new\s+\w+\[\s*0\s*\]\s*;?$", # result := new int[0];
        r"^result\s*:=\s*\[\]\s*;?$",                # result := [];
        r"^result\s*:=\s*\{\}\s*;?$",                # result := {};
        r"^result\s*:=\s*null\s*;?$",                # result := null;
        
        # Return statements with default values
        r"^return\s+0\s*;?$",                        # return 0;
        r"^return\s+false\s*;?$",                    # return false;
        r"^return\s+true\s*;?$",                     # return true;
        r'^return\s+""\s*;?$',                       # return "";
        r"^return\s+new\s+\w+\[\s*0\s*\]\s*;?$",     # return new int[0];
        r"^return\s+\[\]\s*;?$",                     # return [];
        r"^return\s+\{\}\s*;?$",                     # return {};
        r"^return\s+null\s*;?$",                     # return null;
        
        # Multiple simple assignments (for methods with multiple return values)
        r"^(result\d*\s*:=\s*(?:0|false|true|\"\"|null|\[\]|\{\}|new\s+\w+\[\s*0\s*\])\s*;\s*)+$",
    ]
    
    for pattern in simple_return_patterns:
        if re.match(pattern, normalized, re.IGNORECASE):
            return True
    
    return False


def analyze_method_body(body: str) -> Tuple[str, bool]:
    """
    Analyze method body and return (category, is_problematic).

    Categories:
    - "assume_false": Uses the expected assume {:axiom} false pattern
    - "simple_default": Simple default return values (acceptable)
    - "has_implementation": Has actual implementation code (problematic)

    Returns:
        tuple: (category, is_problematic)
    """
    if is_assume_false(body):
        return ("assume_false", False)
    elif is_simple_default_return(body):
        return ("simple_default", False)
    else:
        return ("has_implementation", True)


def check_dafny_yaml_file(file_path: Path) -> Tuple[List, Dict]:
    """
    Check a single Dafny YAML file and analyze the method.

    Returns:
        tuple: (problematic_methods, method_categories)
        - problematic_methods: List of (name, line_number, body, category, type)
        - method_categories: Dict with counts for each category
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            yaml_content = yaml.safe_load(f)
    except Exception as e:
        print(f"Warning: Could not parse YAML {file_path}: {e}")
        return [], {}

    if not yaml_content:
        return [], {}

    # Extract method from vc-code
    method_name, method_body, method_line = extract_method_from_code(yaml_content)

    problematic = []
    categories = {
        "assume_false": 0,
        "simple_default": 0,
        "has_implementation": 0,
    }

    # Analyze method (if present)
    if method_body:
        category, is_problematic = analyze_method_body(method_body)
        categories[category] += 1

        if is_problematic:
            problematic.append(
                (method_name, method_line, method_body, category, "method")
            )

    return problematic, categories


def main():
    """Main function to check all Dafny YAML files."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Dafny methods in YAML files for implementation quality",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_dafny_methods.py                         # Full analysis with statistics (default directory)
  python3 check_dafny_methods.py /path/to/file.yaml      # Analyze single YAML file
  python3 check_dafny_methods.py /path/to/directory      # Analyze directory
  python3 check_dafny_methods.py --list-implementations  # Only list files with method implementations
  python3 check_dafny_methods.py file.yaml --list-implementations # List implementations for single file
  python3 check_dafny_methods.py --include-problematic   # Include 'poor'/'problematic' dirs
        """,
    )
    parser.add_argument(
        "--list-implementations",
        action="store_true",
        help="Only list files with methods having actual implementations (no statistics)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-implementations)",
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
    files_with_implementations = []
    files_with_assume_false = []

    total_categories = {
        "assume_false": 0,
        "simple_default": 0,
        "has_implementation": 0,
    }

    total_methods = 0
    total_problematic_methods = 0

    # Check each file
    for file_path in yaml_files:
        problematic_methods, categories = check_dafny_yaml_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_methods += sum(categories.values())

        if problematic_methods:
            total_problematic_methods += len(problematic_methods)

        # Track files by category
        if categories.get("has_implementation", 0) > 0:
            files_with_implementations.append(str(file_path))

        if categories.get("assume_false", 0) > 0:
            files_with_assume_false.append(str(file_path))

    # Handle --list-implementations option
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

    # Full analysis mode - Summary
    if not args.quiet:
        print("\n" + "=" * 60)
        print("SUMMARY:")
        print(f"Total YAML files checked: {len(yaml_files)}")
        print(f"Total methods found: {total_methods}")
        print()
        print("Method Analysis:")
        print(f"  ✅ Using assume false (expected): {total_categories['assume_false']}")
        print(f"  ✅ Simple default returns (acceptable): {total_categories['simple_default']}")
        print(
            f"  📝 Has actual implementation: {total_categories['has_implementation']}"
        )
        print()
        print("File Statistics:")
        if total_methods > 0:
            print(
                f"  Files with assume false methods: {len(files_with_assume_false)} ({100 * len(files_with_assume_false) / len(yaml_files):.1f}%)"
            )
            print(
                f"  Files with method implementations: {len(files_with_implementations)} ({100 * len(files_with_implementations) / len(yaml_files):.1f}%)"
            )
        else:
            print("  No methods found in vc-code sections")

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if files_with_implementations:
            with open("dafny_methods_with_implementations.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with methods having actual implementations:\n"
                )
                f.write(
                    "# These methods should typically use 'assume {:axiom} false;' as placeholders\n\n"
                )
                for file_path in files_with_implementations:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(files_with_implementations)} files with method implementations to: dafny_methods_with_implementations.txt"
            )

        if files_with_assume_false:
            with open("dafny_methods_with_assume_false.txt", "w") as f:
                f.write(
                    "# Dafny YAML files with methods using expected assume false pattern:\n"
                )
                f.write("# These methods properly use the placeholder pattern\n\n")
                for file_path in files_with_assume_false:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_assume_false)} files with assume false methods to: dafny_methods_with_assume_false.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if files_with_implementations:
            print("\nFirst 10 files with method implementations:")
            for file_path in files_with_implementations[:10]:
                print(f"  {file_path}")
            if len(files_with_implementations) > 10:
                print(f"  ... and {len(files_with_implementations) - 10} more")

        if files_with_assume_false:
            print("\nFirst 10 files with assume false methods:")
            for file_path in files_with_assume_false[:10]:
                print(f"  {file_path}")
            if len(files_with_assume_false) > 10:
                print(f"  ... and {len(files_with_assume_false) - 10} more")

    result = {
        "files_with_implementations": files_with_implementations,
        "files_with_assume_false": files_with_assume_false,
        "statistics": total_categories,
    }
    
    # Output JSON if requested
    if args.output == "json":
        import json
        print(json.dumps(result, indent=2))
    
    return result


if __name__ == "__main__":
    result = main()
