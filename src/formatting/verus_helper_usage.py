#!/usr/bin/env python3
"""
Script to check if functions in vc-helpers sections are used in vc-spec sections.
"""

import re
import yaml
from pathlib import Path


def extract_function_names(code_section):
    """Extract function names from a code section."""
    if not code_section:
        return set()

    # Pattern to match function definitions
    # Matches: fn function_name(, proof fn function_name(, spec fn function_name(
    function_pattern = r"(?:proof\s+)?(?:spec\s+)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\("

    functions = set()
    for match in re.finditer(function_pattern, code_section):
        functions.add(match.group(1))

    return functions


def extract_function_calls(code_section):
    """Extract function calls from a code section."""
    if not code_section:
        return set()

    # First, remove function definitions to avoid false positives
    # Remove lines that contain function definitions
    lines = code_section.split("\n")
    filtered_lines = []

    for line in lines:
        # Skip lines that contain function definitions
        if re.search(
            r"(?:proof\s+)?(?:spec\s+)?fn\s+[a-zA-Z_][a-zA-Z0-9_]*\s*\(", line
        ):
            continue
        filtered_lines.append(line)

    filtered_code = "\n".join(filtered_lines)

    # Pattern to match function calls, but exclude method calls
    # This pattern matches function calls that are NOT preceded by a dot
    # and NOT part of method calls like arr@.contains()
    call_pattern = r"(?<!\.)(?<!@\.)([a-zA-Z_][a-zA-Z0-9_]*)\s*\("

    calls = set()
    for match in re.finditer(call_pattern, filtered_code):
        func_name = match.group(1)
        # Additional filtering to exclude common built-in functions and keywords
        if func_name not in [
            "if",
            "while",
            "for",
            "match",
            "let",
            "mut",
            "return",
            "assert",
            "assume",
            "forall",
            "exists",
            "old",
            "new",
            "Some",
            "None",
            "true",
            "false",
        ]:
            calls.add(func_name)

    return calls


def check_file(file_path):
    """Check a single YAML file for helper function usage."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Parse YAML
        data = yaml.safe_load(content)

        vc_helpers = data.get("vc-helpers", "")
        vc_spec = data.get("vc-spec", "")

        if not vc_helpers.strip():
            return None  # No helpers to check

        # Extract function names from vc-helpers
        helper_functions = extract_function_names(vc_helpers)

        if not helper_functions:
            return None  # No functions found in helpers

        # Extract function calls from vc-spec
        spec_calls = extract_function_calls(vc_spec)

        # Check which helper functions are called in vc-spec
        used_functions = helper_functions.intersection(spec_calls)
        unused_functions = helper_functions - spec_calls

        return {
            "file": file_path,
            "helper_functions": helper_functions,
            "spec_calls": spec_calls,
            "used_functions": used_functions,
            "unused_functions": unused_functions,
        }

    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return None


def main():
    """Main function to check all YAML files."""
    yaml_dir = Path("benchmarks/verus/humaneval/yaml")

    if not yaml_dir.exists():
        print(f"Directory {yaml_dir} does not exist")
        return

    results = []
    files_with_helpers = 0
    files_with_used_helpers = 0

    print("Checking YAML files for helper function usage...")
    print("=" * 60)

    for yaml_file in sorted(yaml_dir.glob("*.yaml")):
        result = check_file(yaml_file)
        if result is not None:
            files_with_helpers += 1
            results.append(result)

            if result["used_functions"]:
                files_with_used_helpers += 1
                print(f"\n📁 {result['file'].name}")
                print(f"   Helper functions: {sorted(result['helper_functions'])}")
                print(f"   Used in vc-spec: {sorted(result['used_functions'])}")
                print(f"   Unused: {sorted(result['unused_functions'])}")
            else:
                print(f"✓ {result['file'].name}: No helper functions used in vc-spec")
                if result["helper_functions"]:
                    print(
                        f"   Helper functions found: {sorted(result['helper_functions'])}"
                    )
                    print(
                        f"   Function calls in vc-spec: {sorted(result['spec_calls'])}"
                    )

    print("\n" + "=" * 60)
    print("Summary:")
    print(f"  Files with vc-helpers: {files_with_helpers}")
    print(f"  Files with used helpers: {files_with_used_helpers}")
    print(
        f"  Files with unused helpers only: {files_with_helpers - files_with_used_helpers}"
    )

    if files_with_used_helpers == 0:
        print("\n🎉 No helper functions are used in vc-spec sections!")
        print("   All functions in vc-helpers can remain where they are.")
    else:
        print(
            f"\n⚠️  {files_with_used_helpers} files have helper functions used in vc-spec"
        )
        print("   These functions should be moved to vc-preamble sections.")

        # Print comma-separated list of files with used helpers
        used_files = [
            result["file"].name for result in results if result["used_functions"]
        ]
        quoted_files = [f'"{filename}"' for filename in used_files]
        print("\nFiles with used helper functions:")
        print(", ".join(quoted_files))


if __name__ == "__main__":
    main()
