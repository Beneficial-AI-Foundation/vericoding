#!/usr/bin/env python3
"""
Script to analyze Lean files and detect definitions that use 'sorry' instead of proper implementations.

This script identifies Lean definitions/theorems in vc-preamble sections that use 'sorry' as a placeholder,
which indicates incomplete or stubbed-out proofs/definitions.

Categories analyzed:
1. 🚀 Proper implementation: Definitions with actual proof/implementation content
2. ⚠️  Uses sorry: Definitions that use 'sorry' as placeholder
3. 🔄 Empty/incomplete: Definitions that are empty or have placeholder patterns

This script:
1. Finds all .lean and .yaml files in the specified directory
2. Extracts definitions, theorems, and lemmas from vc-preamble sections
3. Categorizes each by implementation quality
4. Generates detailed statistics and file lists

Usage:
    python3 check_lean_definitions.py                        # Full analysis with statistics
    python3 check_lean_definitions.py --list-sorry           # Only list files with sorry definitions
    python3 check_lean_definitions.py --list-sorry --quiet   # List sorry files without headers
    python3 check_lean_definitions.py --help                 # Show all options

Output (full analysis mode):
- Console summary with detailed statistics
- lean_definitions_with_sorry.txt: Files containing definitions with sorry
- lean_definitions_with_placeholders.txt: Files with other placeholder patterns
- lean_proper_implementations.txt: Files with proper implementations
"""

import os
import re
import argparse
from pathlib import Path
from typing import List, Tuple, Dict


def find_lean_files(directory: str, exclude_problematic: bool = True) -> List[Path]:
    """Find all .lean and .yaml files in the given directory and subdirectories.

    Args:
        directory: Root directory to search
        exclude_problematic: If True, exclude files in directories with problematic names
    """
    lean_files = []

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
            if file.endswith(".lean") or file.endswith(".yaml"):
                lean_files.append(Path(root) / file)

    return lean_files


def extract_lean_definitions(
    content: str, is_yaml: bool = False
) -> List[Tuple[str, str, int, str]]:
    """
    Extract Lean definition names and their bodies from content.
    Returns list of tuples: (name, body, line_number, type)
    """
    definitions = []

    if is_yaml:
        # For YAML files, extract from multiple sections
        sections_to_check = ["vc-preamble"]
        all_lean_content = []
        
        for section in sections_to_check:
            section_match = re.search(
                rf"{section}:\s*\|-?\s*\n(.*?)(?=\nvc-|$)", content, re.DOTALL
            )
            if section_match:
                section_content = section_match.group(1)
                section_start_line = content[: section_match.start()].count("\n") + 1
                all_lean_content.append((section_content, section_start_line))
        
        if not all_lean_content:
            return definitions
        
        # Process each section
        for lean_content, preamble_start_line in all_lean_content:
            definitions.extend(extract_definitions_from_content(lean_content, preamble_start_line))
        
        return definitions
    else:
        # For .lean files, use the entire content
        lean_content = content
        preamble_start_line = 0
        return extract_definitions_from_content(lean_content, preamble_start_line)


def extract_definitions_from_content(lean_content: str, preamble_start_line: int) -> List[Tuple[str, str, int, str]]:
    """Extract definitions from Lean content."""
    definitions = []
    
    # Patterns to match Lean definitions, theorems, lemmas, etc.
    # Updated patterns to handle complex type signatures and multiline bodies
    lean_patterns = [
        # def name ... := body
        r"(def)\s+(\w+).*?:=\s*(.*?)(?=\n\s*(?:def|theorem|lemma|instance|\Z))",
        # theorem name : type := proof  
        r"(theorem)\s+(\w+).*?:.*?:=\s*(.*?)(?=\n\s*(?:def|theorem|lemma|instance|\Z))",
        # lemma name : type := proof
        r"(lemma)\s+(\w+).*?:.*?:=\s*(.*?)(?=\n\s*(?:def|theorem|lemma|instance|\Z))",
        # instance [name] : type := body
        r"(instance)\s+(?:(\w+)\s+)?.*?:.*?:=\s*(.*?)(?=\n\s*(?:def|theorem|lemma|instance|\Z))",
    ]

    for pattern in lean_patterns:
        for match in re.finditer(pattern, lean_content, re.MULTILINE | re.DOTALL):
            def_type = match.group(1)
            def_name = match.group(2) if match.group(2) else f"anonymous_{def_type}"
            
            # The body is always in the last group for our new patterns
            body = match.group(3).strip() if len(match.groups()) >= 3 else ""

            line_number = (
                preamble_start_line + lean_content[: match.start()].count("\n") + 1
            )
            definitions.append((def_name, body, line_number, def_type))

    return definitions


def has_sorry(body: str) -> bool:
    """
    Check if a definition body uses 'sorry'.
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"--.*$", "", body, flags=re.MULTILINE)  # Remove line comments
    normalized = re.sub(
        r"/\*.*?\*/", "", normalized, flags=re.DOTALL
    )  # Remove block comments
    normalized = re.sub(r"\s+", " ", normalized).strip()  # Normalize whitespace

    # Check for sorry patterns
    sorry_patterns = [
        r"\bsorry\b",
        r"by\s+sorry",
        r":=\s+sorry",
        r"exact\s+sorry",
    ]

    for pattern in sorry_patterns:
        if re.search(pattern, normalized, re.IGNORECASE):
            return True

    return False


def is_placeholder(body: str) -> bool:
    """
    Check if a definition body uses other placeholder patterns.
    """
    # Normalize whitespace and remove comments
    normalized = re.sub(r"--.*$", "", body, flags=re.MULTILINE)
    normalized = re.sub(r"/\*.*?\*/", "", normalized, flags=re.DOTALL)
    normalized = re.sub(r"\s+", " ", normalized).strip()

    # Check if empty or very short
    if not normalized or len(normalized) < 3:
        return True

    # Placeholder patterns (excluding sorry which is handled separately)
    placeholder_patterns = [
        r"\?\?\?",
        r"undefined",
        r"todo",
        r"admit",
        r"_",  # Underscore placeholder
    ]

    for pattern in placeholder_patterns:
        if re.search(pattern, normalized, re.IGNORECASE):
            return True

    return False


def analyze_lean_definition(body: str, def_type: str = "") -> Tuple[str, bool]:
    """
    Analyze Lean definition body and return (category, is_problematic).

    Categories:
    - "uses_sorry": Uses sorry as placeholder
    - "placeholder": Uses other placeholder patterns or is empty
    - "proper_implementation": Has meaningful implementation content

    Returns:
        tuple: (category, is_problematic)
        
    Note: Sorry in theorems/lemmas is acceptable (proofs can be incomplete),
          but sorry in definitions is problematic (definitions should be complete).
    """
    # Check if this is a theorem or lemma (proofs can use sorry acceptably)
    is_proof = def_type.lower() in ["theorem", "lemma"]
    
    if has_sorry(body):
        if is_proof:
            # Sorry in proofs is acceptable - theorems can have incomplete proofs
            return ("uses_sorry", False)
        else:
            # Sorry in definitions is problematic - definitions should be complete
            return ("uses_sorry", True)
    elif is_placeholder(body):
        if is_proof:
            # Empty/placeholder proofs are acceptable
            return ("placeholder", False)
        else:
            # Empty/placeholder definitions are problematic
            return ("placeholder", True)
    else:
        return ("proper_implementation", False)


def check_lean_file(file_path: Path) -> Tuple[List, Dict]:
    """
    Check a single Lean file and analyze all definitions.

    Returns:
        tuple: (problematic_definitions, categories)
        - problematic_definitions: List of (name, line_number, body, category, type)
        - categories: Dict with counts for each category
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
    except (UnicodeDecodeError, PermissionError) as e:
        print(f"Warning: Could not read {file_path}: {e}")
        return [], {}

    is_yaml = file_path.suffix == ".yaml"
    definitions = extract_lean_definitions(content, is_yaml)

    problematic = []
    categories = {"proper_implementation": 0, "uses_sorry": 0, "placeholder": 0}

    for def_name, body, line_number, def_type in definitions:
        category, is_problematic = analyze_lean_definition(body, def_type)
        categories[category] += 1

        if is_problematic:
            problematic.append((def_name, line_number, body, category, def_type))

    return problematic, categories


def main():
    """Main function to check all Lean files."""
    # Parse command line arguments
    parser = argparse.ArgumentParser(
        description="Analyze Lean files and detect definitions using sorry",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 check_lean_definitions.py                       # Full analysis with statistics (default directory)
  python3 check_lean_definitions.py /path/to/file.lean    # Analyze single Lean file
  python3 check_lean_definitions.py /path/to/directory    # Analyze directory
  python3 check_lean_definitions.py --list-sorry          # Only list files with sorry definitions
  python3 check_lean_definitions.py file.lean --list-sorry # List sorry for single file
  python3 check_lean_definitions.py --include-problematic # Include 'poor'/'non_compiling' dirs
        """,
    )
    parser.add_argument(
        "--list-sorry",
        action="store_true",
        help="Only list files with definitions using sorry (no statistics)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Quiet mode: minimal output (useful with --list-sorry)",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default="benchmarks/lean",
        help="Lean file or directory to check (default: %(default)s)",
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
        help="Include files in 'poor', 'non_compiling', etc. directories (default: exclude them)",
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
        if not (check_path.endswith(".lean") or check_path.endswith(".yaml")):
            print(f"Error: {check_path} is not a Lean or YAML file")
            return

        lean_files = [Path(check_path)]
        if not args.quiet:
            print(f"Checking single Lean file: {check_path}")
            print("=" * 60)
    else:
        # Directory mode
        if not args.quiet:
            print(f"Checking Lean files in: {check_path}")
            print("=" * 60)

        # Find all Lean files
        exclude_problematic = not args.include_problematic
        lean_files = find_lean_files(
            check_path, exclude_problematic=exclude_problematic
        )
        if not args.quiet:
            excluded_note = (
                " (excluding problematic directories)"
                if exclude_problematic
                else " (including all directories)"
            )
            print(f"Found {len(lean_files)} Lean files{excluded_note}")

    # Track statistics
    files_with_sorry = []
    files_with_placeholders = []
    files_with_proper_impls = []

    total_categories = {"proper_implementation": 0, "uses_sorry": 0, "placeholder": 0}

    total_definitions = 0
    total_problematic_definitions = 0

    # Check each file
    for file_path in lean_files:
        problematic_definitions, categories = check_lean_file(file_path)

        # Update totals
        for category, count in categories.items():
            total_categories[category] += count

        total_definitions += sum(categories.values())

        if problematic_definitions:
            total_problematic_definitions += len(problematic_definitions)

        # Track files by category
        if categories.get("uses_sorry", 0) > 0:
            files_with_sorry.append(str(file_path))

        if categories.get("placeholder", 0) > 0:
            files_with_placeholders.append(str(file_path))

        if categories.get("proper_implementation", 0) > 0:
            files_with_proper_impls.append(str(file_path))

    # Handle --list-sorry option
    if args.list_sorry:
        if not args.quiet:
            print(
                f"\nFiles with definitions using sorry ({len(files_with_sorry)} files):"
            )
            print("=" * 60)

        for file_path in files_with_sorry:
            print(file_path)

        if not args.quiet:
            print(f"\nTotal: {len(files_with_sorry)} files with sorry definitions")

        return {"files_with_sorry": files_with_sorry, "count": len(files_with_sorry)}

    # Full analysis mode - Summary
    if not args.quiet:
        print("\n" + "=" * 60)
        print("SUMMARY:")
        print(f"Total files checked: {len(lean_files)}")
        print(f"Total definitions/theorems/lemmas found: {total_definitions}")
        print()
        print("Definition Analysis:")
        print(
            f"  🚀 Proper implementation (meaningful content): {total_categories['proper_implementation']}"
        )
        print(f"  ⚠️  Uses sorry (incomplete proofs): {total_categories['uses_sorry']}")
        print(
            f"  🔄 Placeholder (empty or other placeholders): {total_categories['placeholder']}"
        )
        print()
        print("File Statistics:")
        if total_definitions > 0:
            print(
                f"  Files with proper implementations: {len(files_with_proper_impls)} ({100 * len(files_with_proper_impls) / len(lean_files):.1f}%)"
            )
            print(
                f"  Files with sorry definitions: {len(files_with_sorry)} ({100 * len(files_with_sorry) / len(lean_files):.1f}%)"
            )
            print(
                f"  Files with placeholder definitions: {len(files_with_placeholders)} ({100 * len(files_with_placeholders) / len(lean_files):.1f}%)"
            )
        else:
            print("  No definitions/theorems/lemmas found in the analyzed files")

    # Write detailed results to files (only in full analysis mode)
    if not args.quiet:
        if files_with_sorry:
            with open("lean_definitions_with_sorry.txt", "w") as f:
                f.write("# Files with Lean definitions/theorems/lemmas using sorry:\n")
                f.write(
                    "# These definitions should be completed with proper proofs/implementations\n\n"
                )
                for file_path in files_with_sorry:
                    f.write(f"{file_path}\n")

            print(
                f"\n📄 Written {len(files_with_sorry)} files with sorry definitions to: lean_definitions_with_sorry.txt"
            )

        if files_with_placeholders:
            with open("lean_definitions_with_placeholders.txt", "w") as f:
                f.write("# Files with Lean definitions using other placeholders:\n")
                f.write("# These definitions are empty or use placeholder patterns\n\n")
                for file_path in files_with_placeholders:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_placeholders)} files with placeholder definitions to: lean_definitions_with_placeholders.txt"
            )

        if files_with_proper_impls:
            with open("lean_proper_implementations.txt", "w") as f:
                f.write("# Files with proper Lean implementations:\n")
                f.write("# These files contain meaningful definitions/proofs\n\n")
                for file_path in files_with_proper_impls:
                    f.write(f"{file_path}\n")

            print(
                f"📄 Written {len(files_with_proper_impls)} files with proper implementations to: lean_proper_implementations.txt"
            )

    # Show examples (only in full analysis mode)
    if not args.quiet:
        if files_with_sorry:
            print("\nFirst 10 files with sorry definitions:")
            for file_path in files_with_sorry[:10]:
                print(f"  {file_path}")
            if len(files_with_sorry) > 10:
                print(f"  ... and {len(files_with_sorry) - 10} more")

        if files_with_placeholders:
            print("\nFirst 10 files with placeholder definitions:")
            for file_path in files_with_placeholders[:10]:
                print(f"  {file_path}")
            if len(files_with_placeholders) > 10:
                print(f"  ... and {len(files_with_placeholders) - 10} more")

    result = {
        "files_with_sorry": files_with_sorry,
        "files_with_placeholders": files_with_placeholders,
        "files_with_proper_impls": files_with_proper_impls,
        "statistics": total_categories,
    }
    
    # Output JSON if requested
    if args.output == "json":
        import json
        print(json.dumps(result, indent=2))
    
    return result


if __name__ == "__main__":
    result = main()
