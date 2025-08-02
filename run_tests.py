#!/usr/bin/env python3
"""
Simple test runner script for local development.
Usage:
    python run_tests.py                    # Run tests without coverage
    python run_tests.py --coverage         # Run tests with coverage
    python run_tests.py --coverage-html    # Run tests with HTML coverage report
    python run_tests.py [pytest-args]      # Pass additional pytest arguments
"""

import subprocess
import sys
from pathlib import Path


def main():
    """Run tests using pytest."""
    project_root = Path(__file__).parent

    # Check for coverage flags
    if "--coverage-html" in sys.argv:
        pytest_args = [
            "tests/",
            "-v",
            "--tb=short",
            "--cov=vericoding",
            "--cov-report=html",
            "--cov-report=term-missing",
        ]
        sys.argv.remove("--coverage-html")
    elif "--coverage" in sys.argv:
        pytest_args = [
            "tests/",
            "-v",
            "--tb=short",
            "--cov=vericoding",
            "--cov-report=term-missing",
        ]
        sys.argv.remove("--coverage")
    else:
        # Default pytest arguments
        pytest_args = [
            "tests/",
            "-v",
            "--tb=short",
        ]

    # Add any additional arguments passed to this script
    if len(sys.argv) > 1:
        pytest_args.extend(sys.argv[1:])

    # Run pytest
    cmd = ["uv", "run", "pytest"] + pytest_args
    print(f"Running: {' '.join(cmd)}")

    result = subprocess.run(cmd, cwd=project_root)

    # If HTML coverage was generated, show the path
    if "--cov-report=html" in pytest_args:
        html_path = project_root / "htmlcov" / "index.html"
        if html_path.exists():
            print(f"\n📊 Coverage report generated: {html_path}")
            print(f"   Open in browser: file://{html_path.absolute()}")

    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
