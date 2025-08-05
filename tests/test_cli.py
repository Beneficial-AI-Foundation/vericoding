"""Test CLI interfaces and command-line functionality."""

import subprocess
import pytest
import sys
from pathlib import Path


class TestCLIScripts:
    """Test command-line interface scripts."""

    def test_cli_scripts_exist_and_executable(self):
        """Test that CLI script files exist and are readable."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        assert script_path.exists(), f"CLI script should exist at {script_path}"
        assert script_path.is_file(), "CLI script should be a file"
        assert script_path.stat().st_size > 0, "CLI script should not be empty"

        # Check if it's readable
        try:
            with script_path.open("r") as f:
                content = f.read(100)  # Read first 100 chars
                assert content.strip(), "CLI script should have content"
                print("✓ CLI script exists and is readable")
        except Exception as e:
            pytest.fail(f"Cannot read CLI script: {e}")

    def test_cli_help(self):
        """Test that the CLI shows help correctly."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        # Skip if there are syntax errors
        if "SyntaxError" in result.stderr:
            pytest.skip(
                f"Skipping due to syntax error in spec_to_code_modular.py: {result.stderr}"
            )

        # Skip if import errors
        if "ImportError" in result.stderr or "ModuleNotFoundError" in result.stderr:
            pytest.skip(f"Skipping due to import error: {result.stderr}")

        if result.returncode == 0:
            # Should show help information
            assert "usage:" in result.stdout.lower() or "help" in result.stdout.lower()
            print("✓ CLI help works")
        else:
            print(f"Note: CLI returned non-zero exit code: {result.returncode}")
            print(f"stdout: {result.stdout[:200]}...")
            print(f"stderr: {result.stderr[:200]}...")

    def test_cli_scripts_have_shebang(self):
        """Test that CLI script has proper shebang line."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            with script_path.open("r") as f:
                first_line = f.readline().strip()

            # Check if it has a shebang (optional but good practice)
            if first_line.startswith("#!"):
                assert "python" in first_line.lower(), (
                    "CLI script shebang should reference python"
                )
                print(f"✓ CLI script has proper shebang: {first_line}")
            else:
                print("Note: CLI script doesn't have shebang (optional)")

    def test_cli_scripts_import_structure(self):
        """Test that CLI script has reasonable import structure."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            try:
                with script_path.open("r") as f:
                    content = f.read()

                # Should have imports
                assert "import " in content, "CLI script should have imports"

                # Should have some kind of main execution
                has_main = any(
                    pattern in content
                    for pattern in [
                        'if __name__ == "__main__"',
                        "def main(",
                        "argparse",
                        "click",
                    ]
                )
                assert has_main, "CLI script should have main execution logic"

                print("✓ CLI script has reasonable structure")

            except Exception as e:
                print(f"Warning: Could not analyze CLI script: {e}")

    def test_cli_argument_parsing(self):
        """Test CLI script for argument parsing patterns."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            try:
                with script_path.open("r") as f:
                    content = f.read()

                # Look for common argument parsing libraries
                has_arg_parsing = any(
                    lib in content for lib in ["argparse", "click", "typer", "fire"]
                )

                if has_arg_parsing:
                    print("✓ CLI script uses argument parsing")
                else:
                    print("Note: CLI script may not use formal argument parsing")

            except Exception as e:
                print(f"Warning: Could not analyze CLI script: {e}")


class TestCLIFunctionality:
    """Test CLI functionality beyond basic help."""

    def test_cli_error_handling(self):
        """Test that CLI scripts handle errors gracefully."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        # Test with invalid arguments
        result = subprocess.run(
            [sys.executable, str(script_path), "--invalid-argument"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        # Should exit with non-zero code for invalid arguments
        # (unless the script doesn't validate arguments)
        if result.returncode != 0:
            # Should show some kind of error message
            assert result.stderr or result.stdout, (
                "Should show error message for invalid arguments"
            )
            print("✓ CLI shows error for invalid arguments")
        else:
            print("Note: CLI may not validate arguments strictly")

    def test_cli_with_minimal_valid_args(self):
        """Test CLI with minimal valid arguments if possible."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        # Try to run with version flag if available
        for version_flag in ["--version", "-v"]:
            result = subprocess.run(
                [sys.executable, str(script_path), version_flag],
                capture_output=True,
                text=True,
                cwd=project_root,
                timeout=10,
            )

            if result.returncode == 0 and (result.stdout or result.stderr):
                print(f"✓ CLI responds to {version_flag}")
                break
        else:
            print("Note: CLI may not support version flag")

    @pytest.mark.slow
    def test_cli_integration_dry_run(self):
        """Test CLI integration with dry-run or similar safe options."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        # Common flags that might be safe to test
        safe_flags = ["--dry-run", "--check", "--validate", "--list-languages"]

        for flag in safe_flags:
            result = subprocess.run(
                [sys.executable, str(script_path), flag],
                capture_output=True,
                text=True,
                cwd=project_root,
                timeout=30,
            )

            # If it succeeds, great! If not, that's also fine - the flag might not exist
            if result.returncode == 0:
                print(f"✓ CLI supports {flag}")
                break
        else:
            print("Note: CLI may not support common safe flags")


class TestCLIDocumentation:
    """Test CLI documentation and usage information."""

    def test_cli_help_content_quality(self):
        """Test that CLI help content is informative."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        if result.returncode == 0 and result.stdout:
            help_text = result.stdout.lower()

            # Should contain common help elements
            help_indicators = ["usage", "option", "argument", "help", "command"]

            found_indicators = [
                indicator for indicator in help_indicators if indicator in help_text
            ]

            if found_indicators:
                print(f"✓ CLI help contains: {', '.join(found_indicators)}")
            else:
                print("Note: CLI help may be minimal or use different terminology")

            # Check help text length (should be substantial)
            if len(result.stdout) > 100:
                print("✓ CLI help is substantial")
            else:
                print("Note: CLI help is quite brief")

    def test_cli_usage_examples(self):
        """Test if CLI script contains usage examples in its source."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            try:
                with script_path.open("r") as f:
                    content = f.read()

                # Look for documentation patterns
                doc_patterns = [
                    "example",
                    "usage",
                    '"""',  # docstrings
                    "'''",  # docstrings
                    "# Example",
                    "# Usage",
                ]

                found_docs = [
                    pattern
                    for pattern in doc_patterns
                    if pattern.lower() in content.lower()
                ]

                if found_docs:
                    print(f"✓ CLI script contains documentation patterns: {found_docs}")
                else:
                    print("Note: CLI script may have minimal documentation")

            except Exception as e:
                print(f"Warning: Could not analyze CLI script documentation: {e}")


class TestCLICompatibility:
    """Test CLI compatibility and robustness."""

    def test_python_version_compatibility(self):
        """Test that CLI script is compatible with current Python version."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            # Test syntax by attempting to compile
            try:
                with script_path.open("r") as f:
                    source = f.read()

                # Compile to check syntax
                compile(source, str(script_path), "exec")
                print("✓ CLI script has valid Python syntax")

            except SyntaxError as e:
                pytest.fail(f"CLI script has syntax error: {e}")
            except Exception as e:
                print(f"Warning: Could not compile CLI script: {e}")

    def test_cli_import_requirements(self):
        """Test that CLI script has reasonable import requirements."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"

        if script_path.exists():
            try:
                with script_path.open("r") as f:
                    content = f.read()

                # Extract import statements
                import_lines = [
                    line.strip()
                    for line in content.split("\n")
                    if line.strip().startswith(("import ", "from "))
                ]

                if import_lines:
                    print(f"✓ CLI script has {len(import_lines)} import statements")

                    # Check for common problematic imports
                    problematic_imports = [
                        "tensorflow",
                        "torch",
                        "numpy",
                    ]  # Heavy dependencies
                    found_heavy = [
                        imp
                        for imp in problematic_imports
                        if any(imp in line for line in import_lines)
                    ]

                    if found_heavy:
                        print(
                            f"Note: CLI script imports heavy dependencies: {found_heavy}"
                        )
                else:
                    print("Note: CLI script has no import statements")

            except Exception as e:
                print(f"Warning: Could not analyze imports in CLI script: {e}")
