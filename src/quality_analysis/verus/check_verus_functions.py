#!/usr/bin/env python3
"""
Script to analyze Verus function bodies in benchmarks/verus and categorize them:

Expected pattern:
{
    assume(false);
    unreached()
}

Categories analyzed:
1. ✅ Required pattern: Functions with exactly "assume(false); unreached()"
2. ⚠️  Incomplete assume: Functions with "assume(false)" but missing "unreached()"
3. 🚀 Actual implementation: Functions with real code (no assume(false))

This script:
1. Finds all .rs files in the benchmarks/verus directory
2. Extracts function bodies (excluding spec functions and main)
3. Categorizes each function body by implementation type
4. Generates detailed statistics and file lists

Usage:
    python3 check_verus_functions.py                      # Full analysis with statistics (default directory)
    python3 check_verus_functions.py /path/to/file.rs     # Analyze single Rust file
    python3 check_verus_functions.py /path/to/directory   # Analyze directory
    python3 check_verus_functions.py --list-impl          # Only list files with implementations
    python3 check_verus_functions.py file.rs --list-impl  # List implementations for single file
    python3 check_verus_functions.py --help               # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- non_compliant_files.txt: Files not following the required pattern
- files_with_implementations.txt: Files containing actual implementations
- files_with_incomplete_assume.txt: Files with assume(false) but missing unreached()
"""

import os
import re
import argparse
from pathlib import Path
from typing import List, Tuple


def find_rust_files(directory: str, exclude_problematic: bool = True) -> List[Path]:
    """Find all .rs files in the given directory and subdirectories.

    Args:
        directory: Root directory to search
        exclude_problematic: If True, exclude files in directories with problematic names
    """
    rust_files = []

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
            if file.endswith(".rs"):
                rust_files.append(Path(root) / file)

    return rust_files


def extract_function_bodies(content: str) -> List[Tuple[str, str, int]]:
    """
    Extract function names and their bodies from Rust code.
    Returns list of tuples: (function_name, body, line_number)
    """
    functions = []

    # Strategy: Find function names, then look for corresponding vc-code blocks
    # First, find all function declarations (excluding spec functions and proof functions)
    fn_header_pattern = r"fn\s+(\w+)\s*\([^)]*\)"

    function_names = []
    for match in re.finditer(fn_header_pattern, content, re.MULTILINE):
        fn_name = match.group(1)
        if fn_name == "main":  # Skip main function
            continue

        # Check if this is a spec function or proof function by looking at the context before the match
        start_pos = match.start()
        line_start = content.rfind("\n", 0, start_pos) + 1
        line_content = content[line_start : match.end()]

        # Skip if it's a spec function or proof function
        if "spec fn" in line_content or "proof fn" in line_content:
            continue

        line_number = content[:start_pos].count("\n") + 1
        function_names.append((fn_name, line_number))

    # Then, find all vc-code blocks (handle nested braces properly)
    vc_code_blocks = []
    vc_code_starts = []

    # Find all vc-code start positions
    for match in re.finditer(r"//\s*<vc-code>\s*\n?\s*\{", content):
        vc_code_starts.append(match.end() - 1)  # Position of the opening brace

    # For each vc-code start, find the matching closing brace
    for start_pos in vc_code_starts:
        brace_count = 1
        pos = start_pos + 1
        body_start = pos

        while pos < len(content) and brace_count > 0:
            if content[pos] == "{":
                brace_count += 1
            elif content[pos] == "}":
                brace_count -= 1
            pos += 1

        if brace_count == 0:
            # Extract the function body (excluding the braces)
            body = content[body_start : pos - 1].strip()
            vc_code_blocks.append(body)

    # Match function names with vc-code blocks
    # Assume they appear in the same order (which should be true for these files)
    for i, (fn_name, line_number) in enumerate(function_names):
        if i < len(vc_code_blocks):
            functions.append((fn_name, vc_code_blocks[i], line_number))
        else:
            # If no vc-code block, try to find the function body the traditional way
            # Look for the function and extract its body
            simple_pattern = (
                rf"fn\s+{re.escape(fn_name)}\s*\([^)]*\)[^{{]*\{{([^}}]*)\}}"
            )
            match = re.search(simple_pattern, content, re.MULTILINE | re.DOTALL)
            if match:
                functions.append((fn_name, match.group(1).strip(), line_number))

    return functions


def analyze_function_body(body: str) -> Tuple[str, bool]:
    """
    Analyze function body and return (category, matches_required_pattern).

    Categories:
    - "required_pattern": Has exactly "assume(false); unreached()" or contains both proof blocks and the pattern
    - "has_assume_false": Has assume(false) but not the full required pattern
    - "actual_implementation": Has actual code implementation (no assume(false))

    Returns:
        tuple: (category, matches_required_pattern)
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"//.*$", "", body, flags=re.MULTILINE)  # Remove line comments
    normalized = re.sub(
        r"/\*.*?\*/", "", normalized, flags=re.DOTALL
    )  # Remove block comments
    normalized = re.sub(r"\s+", " ", normalized).strip()  # Normalize whitespace

    # Check for the exact required pattern
    required_pattern = r"assume\s*\(\s*false\s*\)\s*;\s*unreached\s*\(\s*\)"
    has_required_pattern = bool(re.search(required_pattern, normalized))

    # Check if it starts with the required pattern (exact match)
    matches_exactly = bool(re.match(required_pattern, normalized))

    if matches_exactly:
        return ("required_pattern", True)

    # Check if it has both proof blocks and the required pattern (also acceptable)
    if has_required_pattern and "proof" in normalized.lower():
        return ("required_pattern", True)

    # Check if it has assume(false) but not the full pattern
    if "assume" in normalized.lower() and "false" in normalized:
        return ("has_assume_false", False)

    # If it doesn't have assume(false), consider it actual implementation
    return ("actual_implementation", False)


def check_function_body(body: str) -> bool:
    """
    Check if function body matches the required pattern (for backward compatibility).
    """
    category, matches = analyze_function_body(body)
    return matches


def check_verus_file(file_path: Path) -> Tuple[List, dict]:
    """
    Check a single Verus file and analyze all functions.

    Returns:
        tuple: (non_compliant_functions, function_categories)
        - non_compliant_functions: List of (function_name, line_number, actual_body)
        - function_categories: Dict with counts for each category
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
    except (UnicodeDecodeError, PermissionError) as e:
        print(f"Warning: Could not read {file_path}: {e}")
        return [], {}

    functions = extract_function_bodies(content)
    non_compliant = []
    categories = {
        "required_pattern": 0,
        "has_assume_false": 0,
        "actual_implementation": 0,
    }

    for fn_name, body, line_number in functions:
        category, matches_required = analyze_function_body(body)
        categories[category] += 1

        if not matches_required:
            non_compliant.append((fn_name, line_number, body, category))

    return non_compliant, categories


def main():
    """Main function to check all Verus files."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Verus function bodies and categorize implementation types",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_verus_functions.py                        # Full analysis with statistics (default directory)
  python3 check_verus_functions.py /path/to/file.rs       # Analyze single Rust file
  python3 check_verus_functions.py /path/to/directory     # Analyze directory
  python3 check_verus_functions.py --list-impl            # Only list files with implementations
  python3 check_verus_functions.py file.rs --list-impl    # List implementations for single file
  python3 check_verus_functions.py --include-problematic  # Include 'poor'/'non_compiling' dirs
        """,
    )
    parser.add_argument(
        "--list-impl",
        action="store_true",
        help="Only list files with actual implementations (no statistics)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-impl)",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default="vericoding/benchmarks/verus",
        help="Rust file or directory to check (default: %(default)s)",
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
        if not check_path.endswith(".rs"):
            print(f"Error: {check_path} is not a Rust file")
            return

        rust_files = [Path(check_path)]
        if not args.quiet:
            print(f"Checking single Verus Rust file: {check_path}")
            print("=" * 60)
    else:
        # Directory mode
        if not args.quiet:
            print(f"Checking Verus files in: {check_path}")
            print("=" * 60)

        # Find all Rust files
        exclude_problematic = not args.include_problematic
        rust_files = find_rust_files(
            check_path, exclude_problematic=exclude_problematic
        )
        if not args.quiet:
            excluded_note = (
                " (excluding problematic directories)"
                if exclude_problematic
                else " (including all directories)"
            )
            print(f"Found {len(rust_files)} Rust files{excluded_note}")

    # Track statistics
    non_compliant_files = []
    files_with_implementations = []
    files_with_assume_false = []

    total_categories = {
        "required_pattern": 0,
        "has_assume_false": 0,
        "actual_implementation": 0,
    }

    total_functions = 0
    total_non_compliant_functions = 0

    # Check each file
    for file_path in rust_files:
        non_compliant_functions, categories = check_verus_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_functions += sum(categories.values())

        if non_compliant_functions:
            non_compliant_files.append(str(file_path))
            total_non_compliant_functions += len(non_compliant_functions)

        # Track files with actual implementations
        if categories.get("actual_implementation", 0) > 0:
            files_with_implementations.append(str(file_path))

        # Track files with assume(false) but incomplete pattern
        if categories.get("has_assume_false", 0) > 0:
            files_with_assume_false.append(str(file_path))

    # Handle --list-impl option
    if args.list_impl:
        if not args.quiet:
            print(
                f"\nFiles with actual implementations ({len(files_with_implementations)} files):"
            )
            print("=" * 60)

        for file_path in files_with_implementations:
            print(file_path)

        if not args.quiet:
            print(
                f"\nTotal: {len(files_with_implementations)} files with actual implementations"
            )

        result = {
            "files_with_implementations": files_with_implementations,
            "count": len(files_with_implementations),
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
        print(f"Total files checked: {len(rust_files)}")
        print(f"Total functions found: {total_functions}")
        print()
        print("Function Body Analysis:")
        print(
            f"  ✅ Required pattern (assume(false); unreached()): {total_categories['required_pattern']}"
        )
        print(
            f"  ⚠️  Has assume(false) but incomplete: {total_categories['has_assume_false']}"
        )
        print(
            f"  🚀 Actual implementation (no assume(false)): {total_categories['actual_implementation']}"
        )
        print()
        print("File Statistics:")
        print(
            f"  Compliant files: {len(rust_files) - len(non_compliant_files)} ({100 * (len(rust_files) - len(non_compliant_files)) / len(rust_files):.1f}%)"
        )
        print(
            f"  Non-compliant files: {len(non_compliant_files)} ({100 * len(non_compliant_files) / len(rust_files):.1f}%)"
        )
        print(
            f"  Files with actual implementations: {len(files_with_implementations)} ({100 * len(files_with_implementations) / len(rust_files):.1f}%)"
        )

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if non_compliant_files:
            with open("non_compliant_files.txt", "w") as f:
                f.write("# Files that do NOT respect the required pattern:\n")
                f.write("# Expected: { assume(false); unreached() }\n\n")
                for file_path in non_compliant_files:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(non_compliant_files)} non-compliant files to: non_compliant_files.txt"
            )

        if files_with_implementations:
            with open("files_with_implementations.txt", "w") as f:
                f.write(
                    "# Files with actual implementation code (not just assume(false)):\n\n"
                )
                for file_path in files_with_implementations:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_implementations)} files with implementations to: files_with_implementations.txt"
            )

        if files_with_assume_false:
            with open("files_with_incomplete_assume.txt", "w") as f:
                f.write(
                    "# Files with assume(false) but incomplete pattern (missing unreached()):\n\n"
                )
                for file_path in files_with_assume_false:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_assume_false)} files with incomplete assume pattern to: files_with_incomplete_assume.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if non_compliant_files:
            print("\nFirst 10 non-compliant files:")
            for file_path in non_compliant_files[:10]:
                print(f"  {file_path}")
            if len(non_compliant_files) > 10:
                print(f"  ... and {len(non_compliant_files) - 10} more")

        if files_with_implementations:
            print("\nFirst 10 files with actual implementations:")
            for file_path in files_with_implementations[:10]:
                print(f"  {file_path}")
            if len(files_with_implementations) > 10:
                print(f"  ... and {len(files_with_implementations) - 10} more")

    result = {
        "non_compliant_files": non_compliant_files,
        "files_with_implementations": files_with_implementations,
        "files_with_assume_false": files_with_assume_false,
        "statistics": total_categories,
    }

    # Handle JSON output
    if args.output == "json":
        import json

        print(json.dumps(result, indent=2))

    return result


if __name__ == "__main__":
    result = main()
