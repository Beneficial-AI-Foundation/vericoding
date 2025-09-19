#!/usr/bin/env python3
"""
Convenience script to run all quality analysis tools with consistent interface.

This script runs all available quality analysis tools for Verus, Dafny, and Lean
with a unified command-line interface. It supports:

- Single file or directory analysis for each language
- Consistent output formatting (text/json)
- Backward compatibility with old --*-dir options
- Flexible path specification with benchmark root or individual paths

The script runs:
1. Verus function analysis (check_verus_functions.py)
2. Verus spec function analysis (check_spec_functions.py)
3. Verus type validation (check_verus_types.py)
4. Dafny comprehensive YAML analysis (check_dafny_yaml.py)
5. Dafny function/predicate analysis (check_dafny_functions.py)
6. Dafny method analysis (check_dafny_methods.py)
7. Lean definition analysis (check_lean_definitions.py)
"""

import argparse
import subprocess
import sys
from pathlib import Path


def run_script(script_name, args, description):
    """Run a quality analysis script with given arguments."""
    print(f"\n{'=' * 60}")
    print(f"Running {description}")
    print(f"{'=' * 60}")

    cmd = [sys.executable, script_name] + args
    try:
        subprocess.run(cmd, check=True, capture_output=False)
        print(f"✅ {description} completed successfully")
        return True
    except subprocess.CalledProcessError as e:
        print(f"❌ {description} failed with exit code {e.returncode}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Run all quality analysis tools",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 analyze_all.py                                    # Analyze default directories
  python3 analyze_all.py ../../benchmarks                  # Analyze custom benchmark root
  python3 analyze_all.py --verus-path ../../benchmarks/verus/numpy_triple  # Custom Verus path
  python3 analyze_all.py --dafny-path ../../benchmarks/dafny               # Custom Dafny path
  python3 analyze_all.py --quiet                           # Minimal output
  python3 analyze_all.py --output json                     # JSON output format
        """,
    )

    parser.add_argument(
        "benchmark_root",
        nargs="?",
        help="Root directory containing benchmark subdirectories (verus/, dafny/, lean/)",
    )
    parser.add_argument(
        "--verus-path",
        help="Path to Verus files or directory (overrides benchmark_root/verus)",
    )
    parser.add_argument(
        "--dafny-path",
        help="Path to Dafny files or directory (overrides benchmark_root/dafny)",
    )
    parser.add_argument(
        "--lean-path",
        help="Path to Lean files or directory (overrides benchmark_root/lean)",
    )
    parser.add_argument(
        "--quiet", action="store_true", help="Quiet mode for all scripts"
    )
    parser.add_argument(
        "--include-problematic",
        action="store_true",
        help="Include problematic directories in analysis",
    )
    parser.add_argument(
        "--output",
        choices=["text", "json"],
        default="text",
        help="Output format for all scripts (default: text)",
    )

    # Deprecated options for backward compatibility
    parser.add_argument("--verus-dir", help="Deprecated: use --verus-path instead")
    parser.add_argument("--dafny-dir", help="Deprecated: use --dafny-path instead")
    parser.add_argument("--lean-dir", help="Deprecated: use --lean-path instead")

    args = parser.parse_args()

    # Resolve paths with backward compatibility
    def resolve_path(
        new_path, old_path, default_subdir, benchmark_root, old_option_name
    ):
        """Resolve path with priority: new_path > old_path > benchmark_root/subdir > default"""
        if new_path:
            return new_path
        if old_path:
            print(f"Warning: Using deprecated {old_option_name} option")
            return old_path
        if benchmark_root:
            return str(Path(benchmark_root) / default_subdir)
        return f"../../benchmarks/{default_subdir}"

    benchmark_root = args.benchmark_root
    verus_path = resolve_path(
        args.verus_path, args.verus_dir, "verus", benchmark_root, "--verus-dir"
    )
    dafny_path = resolve_path(
        args.dafny_path, args.dafny_dir, "dafny", benchmark_root, "--dafny-dir"
    )
    lean_path = resolve_path(
        args.lean_path, args.lean_dir, "lean", benchmark_root, "--lean-dir"
    )

    # Build common arguments
    common_args = []
    if args.quiet:
        common_args.append("--quiet")
    if args.include_problematic:
        common_args.append("--include-problematic")
    if args.output != "text":
        common_args.extend(["--output", args.output])

    success_count = 0
    total_count = 0

    # 1. Check Verus regular functions
    total_count += 1
    verus_args = [verus_path] + common_args
    if run_script(
        "verus/check_verus_functions.py", verus_args, "Verus Function Analysis"
    ):
        success_count += 1

    # 2. Check Verus spec functions
    total_count += 1
    spec_args = [verus_path] + common_args
    if run_script(
        "verus/check_spec_functions.py", spec_args, "Verus Spec Function Analysis"
    ):
        success_count += 1

    # 3. Check Verus type validation
    total_count += 1
    types_args = [verus_path] + common_args
    if run_script("verus/check_verus_types.py", types_args, "Verus Type Validation"):
        success_count += 1

    # 4. Check Dafny YAML comprehensive analysis
    total_count += 1
    dafny_yaml_args = [dafny_path] + common_args
    if run_script(
        "dafny/check_dafny_yaml.py",
        dafny_yaml_args,
        "Dafny YAML Comprehensive Analysis",
    ):
        success_count += 1

    # 5. Check Dafny functions/predicates
    total_count += 1
    dafny_args = [dafny_path] + common_args
    if run_script(
        "dafny/check_dafny_functions.py",
        dafny_args,
        "Dafny Function/Predicate Analysis",
    ):
        success_count += 1

    # 6. Check Dafny methods
    total_count += 1
    dafny_methods_args = [dafny_path] + common_args
    if run_script(
        "dafny/check_dafny_methods.py", dafny_methods_args, "Dafny Method Analysis"
    ):
        success_count += 1

    # 7. Check Lean definitions
    total_count += 1
    lean_args = [lean_path] + common_args
    if run_script(
        "lean/check_lean_definitions.py", lean_args, "Lean Definition Analysis"
    ):
        success_count += 1

    # Summary
    print(f"\n{'=' * 60}")
    print("ANALYSIS COMPLETE")
    print(f"{'=' * 60}")
    print(f"✅ Successful: {success_count}/{total_count}")
    if success_count < total_count:
        print(f"❌ Failed: {total_count - success_count}/{total_count}")

    print("\nOutput files generated:")
    print("  Verus Analysis:")
    print("    - verus_functions_with_implementations.txt")
    print("    - verus_yaml_spec_functions_with_defaults.txt")
    print("    - verus_yaml_proper_spec_functions.txt")
    print("  Dafny Analysis:")
    print("    - dafny_yaml_functions_with_defaults.txt")
    print("    - dafny_yaml_proper_specifications.txt")
    print("    - dafny_functions_with_defaults.txt")
    print("    - dafny_methods_with_implementations.txt")
    print("    - dafny_methods_with_assume_false.txt")
    print("  Lean Analysis:")
    print("    - lean_definitions_with_sorry.txt")
    print("    - lean_proper_implementations.txt")
    print("  And more detailed analysis files...")

    if success_count == total_count:
        print("\n🎉 All quality analysis tools completed successfully!")
        sys.exit(0)
    else:
        print("\n⚠️  Some analysis tools failed. Check output above for details.")
        sys.exit(1)


if __name__ == "__main__":
    main()
