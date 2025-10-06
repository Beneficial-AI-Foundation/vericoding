#!/usr/bin/env python3
"""Smoke test for vericoder.py across all languages.

Usage: python scripts/test_vericoder_smoke.py [language] [llm] [iterations] [limit]
  language: lean, verus, dafny, config, or 'all' (default: all)
  llm: model name (default: claude-sonnet)
  iterations: number of iterations (default: 1)
  limit: files per language (default: 1)
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path
from typing import List

# Load environment variables from .env file if it exists
try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass  # python-dotenv not available, skip


class Colors:
    """ANSI color codes for terminal output."""

    RED = "\033[0;31m"
    GREEN = "\033[0;32m"
    YELLOW = "\033[1;33m"
    NC = "\033[0m"  # No Color


def print_colored(message: str, color: str = Colors.NC) -> None:
    """Print a colored message to stdout."""
    print(f"{color}{message}{Colors.NC}")


def run_command(cmd: List[str], check: bool = True) -> subprocess.CompletedProcess:
    """Run a command and return the result."""
    return subprocess.run(cmd, check=check, capture_output=False)


def check_api_keys() -> None:
    """Check if any API keys are set and warn if not."""
    api_keys = ["OPENROUTER_API_KEY", "ANTHROPIC_API_KEY", "OPENAI_API_KEY"]
    if not any(os.getenv(key) for key in api_keys):
        print_colored(
            "⚠️  Warning: No API key found. Set OPENROUTER_API_KEY, ANTHROPIC_API_KEY, or OPENAI_API_KEY",
            Colors.YELLOW,
        )
        print("Tests will validate structure only (no LLM calls)")
        print()


def test_lean(llm: str, limit: int, iterations: int) -> bool:
    """Test Lean language support."""
    print_colored("Testing Lean...", Colors.YELLOW)
    test_dir = Path("benchmarks/lean/test")

    if not test_dir.is_dir():
        print_colored("✗ Lean test directory not found", Colors.RED)
        return False

    try:
        run_command(
            [
                "uv",
                "run",
                "src/vericoder.py",
                "lean",
                str(test_dir),
                "--llm",
                llm,
                "--limit",
                str(limit),
                "--iterations",
                str(iterations),
                "--no-wandb",
                "--workers",
                "1",
            ]
        )
        print_colored("✓ Lean test passed", Colors.GREEN)
        return True
    except subprocess.CalledProcessError:
        print_colored("✗ Lean test failed", Colors.RED)
        return False


def test_verus(llm: str, limit: int, iterations: int) -> bool:
    """Test Verus language support."""
    print_colored("Testing Verus...", Colors.YELLOW)

    # Find first available test directory
    for pattern in ["files", "test"]:
        test_dirs = list(Path("benchmarks/verus").rglob(pattern))
        if test_dirs:
            test_dir = test_dirs[0]
            break
    else:
        print_colored("✗ Verus test directory not found", Colors.RED)
        return False

    print(f"Using test directory: {test_dir}")

    try:
        run_command(
            [
                "uv",
                "run",
                "src/vericoder.py",
                "verus",
                str(test_dir),
                "--llm",
                llm,
                "--limit",
                str(limit),
                "--iterations",
                str(iterations),
                "--no-wandb",
                "--workers",
                "1",
            ]
        )
        print_colored("✓ Verus test passed", Colors.GREEN)
        return True
    except subprocess.CalledProcessError:
        print_colored("✗ Verus test failed", Colors.RED)
        return False


def test_dafny(llm: str, limit: int, iterations: int) -> bool:
    """Test Dafny language support."""
    print_colored("Testing Dafny...", Colors.YELLOW)

    # Find first available test directory
    for pattern in ["files", "test"]:
        test_dirs = list(Path("benchmarks/dafny").rglob(pattern))
        if test_dirs:
            test_dir = test_dirs[0]
            break
    else:
        print_colored("✗ Dafny test directory not found", Colors.RED)
        return False

    print(f"Using test directory: {test_dir}")

    try:
        run_command(
            [
                "uv",
                "run",
                "src/vericoder.py",
                "dafny",
                str(test_dir),
                "--llm",
                llm,
                "--limit",
                str(limit),
                "--iterations",
                str(iterations),
                "--no-wandb",
                "--workers",
                "1",
            ]
        )
        print_colored("✓ Dafny test passed", Colors.GREEN)
        return True
    except subprocess.CalledProcessError:
        print_colored("✗ Dafny test failed", Colors.RED)
        return False


def test_config() -> bool:
    """Test configuration loading."""
    print_colored("Testing configuration loading...", Colors.YELLOW)

    test_code = """
from src.vericoding.core.config import ProcessingConfig
from src.vericoding.core.prompts import PromptLoader

languages = ProcessingConfig.get_available_languages()
print(f'✓ Found {len(languages)} language configurations')

for lang_name, lang_config in languages.items():
    print(f'  - {lang_config.name}')
    prompt_loader = PromptLoader(lang_name, prompts_file=lang_config.prompts_file)
    validation = prompt_loader.validate_prompts()
    if not validation.valid:
        print(f'    ✗ Missing prompts: {validation.missing}')
        exit(1)
    print(f'    ✓ {len(validation.available)} prompts loaded')

print('✓ All configurations valid')
"""

    try:
        run_command(["uv", "run", "python", "-c", test_code])
        print_colored("✓ Configuration test passed", Colors.GREEN)
        return True
    except subprocess.CalledProcessError:
        print_colored("✗ Configuration test failed", Colors.RED)
        return False


def main() -> int:
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Smoke test for vericoder.py across all languages"
    )
    parser.add_argument(
        "language",
        nargs="?",
        default="all",
        choices=["all", "lean", "verus", "dafny", "config"],
        help="Language to test (default: all)",
    )
    parser.add_argument(
        "--llm",
        default="claude-sonnet",
        help="LLM model to use (default: claude-sonnet)",
    )
    parser.add_argument(
        "--iterations", type=int, default=1, help="Number of iterations (default: 1)"
    )
    parser.add_argument(
        "--limit", type=int, default=1, help="Files per language (default: 1)"
    )

    args = parser.parse_args()

    print("🧪 Vericoder Smoke Tests")
    print("========================")
    print(f"Language: {args.language}")
    print(f"LLM: {args.llm}")
    print(f"Iterations: {args.iterations}")
    print(f"Files per language: {args.limit}")
    print()

    check_api_keys()

    failed_tests = []

    # Define test functions
    tests = {
        "config": lambda: test_config(),
        "lean": lambda: test_lean(args.llm, args.limit, args.iterations),
        "verus": lambda: test_verus(args.llm, args.limit, args.iterations),
        "dafny": lambda: test_dafny(args.llm, args.limit, args.iterations),
    }

    # Run tests based on selection
    if args.language == "all":
        # Test configuration first
        for test_name in ["config", "lean", "verus", "dafny"]:
            if not tests[test_name]():
                failed_tests.append(test_name)
            print()
    else:
        if not tests[args.language]():
            failed_tests.append(args.language)

    # Print summary
    print("========================")
    if not failed_tests:
        print_colored("✅ All tests passed!", Colors.GREEN)
        return 0
    else:
        print_colored(f"❌ Failed tests: {', '.join(failed_tests)}", Colors.RED)
        return 1


if __name__ == "__main__":
    sys.exit(main())
