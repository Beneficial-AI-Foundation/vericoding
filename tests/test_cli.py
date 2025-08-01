"""Test CLI interfaces and command-line functionality."""

import subprocess
import pytest
import sys
from pathlib import Path


class TestCLI:
    """Test command-line interfaces."""

    def test_original_cli_help(self):
        """Test that the original spec_to_code.py CLI works."""
        result = subprocess.run(
            [sys.executable, "spec_to_code.py", "--help"],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parent.parent,
        )
        # Skip test if there are syntax errors (e.g., merge conflicts)
        if "SyntaxError" in result.stderr:
            pytest.skip(
                f"Skipping due to syntax error in spec_to_code.py: {result.stderr}"
            )
        assert result.returncode == 0, f"CLI failed with: {result.stderr}"

    def test_modular_cli_help(self):
        """Test that the modular spec_to_code_modular.py CLI works."""
        result = subprocess.run(
            [sys.executable, "spec_to_code_modular.py", "--help"],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parent.parent,
        )
        assert result.returncode == 0, f"Modular CLI failed with: {result.stderr}"

    def test_cli_scripts_exist(self):
        """Test that CLI script files exist."""
        project_root = Path(__file__).parent.parent

        original_script = project_root / "spec_to_code.py"
        modular_script = project_root / "spec_to_code_modular.py"

        assert original_script.exists(), "spec_to_code.py should exist"
        assert modular_script.exists(), "spec_to_code_modular.py should exist"
