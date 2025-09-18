#!/usr/bin/env python3
"""Code2Verus: A tool to translate code from various languages to Verus

This tool uses AI models to translate code from languages like Dafny and Lean
to Verus, a verification-aware Rust framework.
"""

import asyncio
import sys
import argparse
from pathlib import Path
from dotenv import load_dotenv
import logfire

from code2verus.processing import main_async
from code2verus.utils import check_verus_availability
from code2verus.agent import translate_code_to_verus, create_agent
from code2verus.verification import verify_verus_code
from code2verus.benchmarks import load_benchmark

# Load environment variables
load_dotenv()

# Configure Logfire only if authentication is available
try:
    logfire.configure()
    logfire.instrument_pydantic_ai()
    print("Logfire configured successfully")
except Exception as e:
    print(f"Logfire configuration skipped: {e}")

__all__ = [
    "main",
    "main_async",
    "translate_code_to_verus",
    "verify_verus_code",
    "load_benchmark",
    "create_agent",
]


def main() -> None:
    """Main entry point with CLI support"""

    # Check for Verus installation
    if not check_verus_availability():
        print("\nFailed to find or run Verus. Please ensure:")
        print("1. Verus is installed and working")
        print("2. The verus_path in config.yml is correct")
        print("3. Verus is in your PATH if using the default 'verus' command")
        sys.exit(1)

    parser = argparse.ArgumentParser(
        description="Translate code between verification languages",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  code2verus                                                    # Use default DafnyBench (dafny->verus)
  code2verus --source-language dafny --target-language verus   # Dafny to Verus (explicit)
  code2verus --source-language verus --target-language dafny   # Verus to Dafny (reverse)
  code2verus --source-language lean --target-language verus    # Lean to Verus
  code2verus --source-language verus --target-language lean    # Verus to Lean
  code2verus --benchmark wendy-sun/DafnyBench --source-language dafny --target-language verus
  code2verus --benchmark sunblaze-ucb/verina --source-language lean --target-language verus
  code2verus --benchmark sunblaze-ucb/verina --source-language verus --target-language lean
  code2verus --benchmark ./benches/verus_examples --source-language verus --target-language dafny
  code2verus --max-concurrent 5                        # Allow 5 concurrent translations
  code2verus --limit 10                                 # Process only the first 10 files

Supported Translation Combinations:
  - dafny -> verus
  - lean -> verus  
  - verus -> dafny
  - verus -> lean

Legacy Examples (deprecated --language flag):
  code2verus --language dafny                          # Same as --source-language dafny --target-language verus


Debug Examples:
  code2verus --save-debug                               # Save debug contexts to JSON files
  code2verus --debug-report                             # Print debug report after each translation
  code2verus --debug-summary --include-debug-in-result # Print overall debug summary at end
  code2verus --save-debug --debug-dir ./my_debug_sessions  # Save debug sessions to custom directory
  code2verus --save-debug --debug-report --debug-summary --include-debug-in-result  # All debug options
        """,
    )
    parser.add_argument(
        "--benchmark",
        default="wendy-sun/DafnyBench",
        help="Hugging Face dataset path or local folder path for the benchmark (default: wendy-sun/DafnyBench)",
    )
    parser.add_argument(
        "--split", default="test", help="Dataset split to use (default: test)"
    )
    parser.add_argument(
        "--source-language",
        default="dafny",
        choices=["dafny", "lean", "verus"],
        help="Source language to translate from (default: dafny)",
    )
    parser.add_argument(
        "--target-language",
        default="verus",
        choices=["dafny", "lean", "verus"],
        help="Target language to translate to (default: verus)",
    )
    parser.add_argument(
        "--language",
        help="Legacy parameter for source language (use --source-language instead). Will be deprecated.",
    )
    parser.add_argument(
        "--max-concurrent",
        type=int,
        default=3,
        help="Maximum number of concurrent translations (default: 3)",
    )
    parser.add_argument(
        "--file-pattern",
        default="*.dfy",
        help="File pattern to match when loading from local folder (default: *.dfy)",
    )
    parser.add_argument(
        "--limit",
        type=int,
        help="Maximum number of files to process (default: process all files)",
    )

    # Debug options
    debug_group = parser.add_argument_group("Debug Options")
    debug_group.add_argument(
        "--save-debug",
        action="store_true",
        help="Save debug contexts to JSON files for later analysis",
    )
    debug_group.add_argument(
        "--debug-dir",
        type=Path,
        default=Path("debug_sessions"),
        help="Directory to save debug sessions (default: debug_sessions)",
    )
    debug_group.add_argument(
        "--debug-report",
        action="store_true",
        help="Generate and print debug reports after each translation",
    )
    debug_group.add_argument(
        "--debug-summary",
        action="store_true",
        help="Print debug summary at the end of processing",
    )
    debug_group.add_argument(
        "--include-debug-in-result",
        action="store_true",
        help="Include debug context in translation results (uses more memory)",
    )

    args = parser.parse_args()

    # Handle backward compatibility with --language flag
    if args.language is not None:
        print("Warning: --language flag is deprecated. Use --source-language instead.")
        args.source_language = args.language

    # Validate language combination
    if args.source_language == args.target_language:
        print(
            f"Error: Source and target languages cannot be the same ({args.source_language})"
        )
        sys.exit(1)

    # For now, only support certain combinations
    supported_combinations = [
        ("dafny", "verus"),
        ("dafny", "lean"),
        ("lean", "verus"),
        ("verus", "dafny"),
        ("verus", "lean"),
    ]

    if (args.source_language, args.target_language) not in supported_combinations:
        print(
            f"Error: Translation from {args.source_language} to {args.target_language} is not yet supported."
        )
        print("Supported combinations:")
        for src, tgt in supported_combinations:
            print(f"  - {src} -> {tgt}")
        sys.exit(1)

    # Auto-determine file pattern based on source language if using default and local folder
    file_pattern = args.file_pattern
    if args.file_pattern == "*.dfy" and Path(args.benchmark).exists():
        if args.source_language == "lean":
            file_pattern = "*.lean"
        elif args.source_language == "dafny":
            file_pattern = "*.dfy"
        elif args.source_language == "verus":
            file_pattern = "*.rs"

    print(f"Using benchmark: {args.benchmark} (split: {args.split})")
    print(f"Translation: {args.source_language} -> {args.target_language}")
    print(f"Max concurrent translations: {args.max_concurrent}")
    if args.limit:
        print(f"File limit: {args.limit}")
    if Path(args.benchmark).exists():
        print(f"File pattern: {file_pattern}")

    # Print debug options if enabled
    if args.save_debug or args.debug_report or args.debug_summary:
        print("Debug options enabled:")
        if args.save_debug:
            print(f"  - Saving debug sessions to: {args.debug_dir}")
        if args.debug_report:
            print("  - Generating debug reports after each translation")
        if args.debug_summary:
            print("  - Will print debug summary at end")
        if args.include_debug_in_result:
            print("  - Including debug context in results")

    # Run the async main function
    asyncio.run(
        main_async(
            benchmark=args.benchmark,
            split=args.split,
            source_language=args.source_language,
            target_language=args.target_language,
            max_concurrent=args.max_concurrent,
            file_pattern=file_pattern,
            limit=args.limit,
            # Debug options
            save_debug=args.save_debug,
            debug_dir=args.debug_dir,
            debug_report=args.debug_report,
            debug_summary=args.debug_summary,
            include_debug_in_result=args.include_debug_in_result,
        )
    )


if __name__ == "__main__":
    main()
