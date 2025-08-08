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
    'main',
    'main_async',
    'translate_code_to_verus',
    'verify_verus_code',
    'load_benchmark',
    'create_agent'
]

# Import public API
from code2verus.agent import translate_code_to_verus, create_agent
from code2verus.verification import verify_verus_code
from code2verus.benchmarks import load_benchmark


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
        description="Translate code to Verus",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  code2verus                                            # Use default DafnyBench (test split, dafny)
  code2verus --benchmark wendy-sun/DafnyBench --language dafny  # Specify language explicitly  
  code2verus --benchmark sunblaze-ucb/verina --language lean --split train  # Use Verina benchmark with Lean
  code2verus --benchmark other-user/CustomBench --language dafny --split test # Use different benchmark
  code2verus --benchmark benches/bignum_specs --language dafny  # Use local folder
  code2verus --benchmark ./benches/numpy_specs --language dafny  # Use local folder with explicit path
  code2verus --max-concurrent 5                        # Allow 5 concurrent translations
        """
    )
    parser.add_argument(
        "--benchmark",
        default="wendy-sun/DafnyBench",
        help="Hugging Face dataset path or local folder path for the benchmark (default: wendy-sun/DafnyBench)"
    )
    parser.add_argument(
        "--split",
        default="test",
        help="Dataset split to use (default: test)"
    )
    parser.add_argument(
        "--language",
        default="dafny",
        choices=["dafny", "lean"],
        help="Source language to translate from (default: dafny)"
    )
    parser.add_argument(
        "--max-concurrent",
        type=int,
        default=3,
        help="Maximum number of concurrent translations (default: 3)"
    )
    parser.add_argument(
        "--file-pattern",
        default="*.dfy",
        help="File pattern to match when loading from local folder (default: *.dfy)"
    )
    
    args = parser.parse_args()
    
    # Auto-determine file pattern based on language if using default and local folder
    file_pattern = args.file_pattern
    if args.file_pattern == "*.dfy" and Path(args.benchmark).exists():
        if args.language == "lean":
            file_pattern = "*.lean"
        elif args.language == "dafny":
            file_pattern = "*.dfy"
    
    print(f"Using benchmark: {args.benchmark} (split: {args.split})")
    print(f"Source language: {args.language}")
    print(f"Max concurrent translations: {args.max_concurrent}")
    if Path(args.benchmark).exists():
        print(f"File pattern: {file_pattern}")
    
    # Run the async main function
    asyncio.run(main_async(
        benchmark=args.benchmark,
        split=args.split, 
        source_language=args.language,
        max_concurrent=args.max_concurrent,
        file_pattern=file_pattern
    ))


if __name__ == "__main__":
    main()
