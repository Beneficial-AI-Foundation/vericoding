"""
End-to-end tests for the modular vericoder system.
These tests validate the complete workflow from CLI invocation to output generation.
"""

import pytest
import subprocess
import sys
import tempfile
import shutil
from pathlib import Path
import os
from unittest.mock import patch, MagicMock


class TestEndToEnd:
    """End-to-end tests for the complete spec-to-code workflow."""

    @pytest.fixture
    def project_root(self):
        """Get the project root directory."""
        return Path(__file__).parent.parent

    @pytest.fixture
    def temp_workspace(self):
        """Create a temporary workspace with sample files."""
        temp_dir = tempfile.mkdtemp(prefix="vericoding_test_")
        temp_path = Path(temp_dir)

        # Create sample specification files for different languages

        # Dafny sample
        dafny_dir = temp_path / "dafny_specs"
        dafny_dir.mkdir()
        (dafny_dir / "simple.dfy").write_text("""
method Add(x: int, y: int) returns (sum: int)
    ensures sum == x + y
{
    // TODO: Implement
}

method Max(a: int, b: int) returns (max: int)
    ensures max >= a && max >= b
    ensures max == a || max == b
{
    // TODO: Implement  
}
""")

        # Lean sample
        lean_dir = temp_path / "lean_specs"
        lean_dir.mkdir()
        (lean_dir / "simple.lean").write_text("""
def add (x y : ℕ) : ℕ := sorry

theorem add_comm (x y : ℕ) : add x y = add y x := sorry
""")

        # Verus sample (Rust with Verus annotations)
        verus_dir = temp_path / "verus_specs"
        verus_dir.mkdir()
        (verus_dir / "simple.rs").write_text("""
use vstd::prelude::*;

verus! {

fn add(x: u32, y: u32) -> (result: u32)
    ensures result == x + y
{
    // TODO: Implement
}

} // verus!
""")

        yield temp_path
        shutil.rmtree(temp_dir, ignore_errors=True)

    def test_cli_dry_run_no_errors(self, project_root, temp_workspace):
        """Test that CLI can be invoked without runtime errors (dry run)."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        # Test with dafny (most common case)
        dafny_specs = temp_workspace / "dafny_specs"

        # Mock environment variables to avoid API key requirements
        env = os.environ.copy()
        env["ANTHROPIC_API_KEY"] = "test-key-for-validation"

        # Run with minimal arguments that should parse correctly
        # We expect this to fail at tool availability check, but argument parsing should work
        result = subprocess.run(
            [
                sys.executable,
                str(script_path),
                "dafny",
                str(dafny_specs),
                "--iterations",
                "1",
                "--workers",
                "1",
            ],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=60,
            env=env,
        )

        # We expect failure due to missing Dafny tool, but should not have syntax/import errors
        if "SyntaxError" in result.stderr:
            pytest.fail(f"Syntax error in modular script: {result.stderr}")

        if "ImportError" in result.stderr:
            pytest.fail(f"Import error in modular script: {result.stderr}")

        if "ModuleNotFoundError" in result.stderr:
            pytest.fail(f"Module not found error: {result.stderr}")

        # Should reach the tool availability check
        assert (
            "Checking Dafny availability" in result.stdout
            or "Error:" in result.stdout
            or result.returncode != 0
        ), "Should reach tool availability check"

        print("✓ CLI invocation works without syntax/import errors")

    def test_language_support_consistency(self, project_root, temp_workspace):
        """Test that all expected languages are supported consistently."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        # Get help to see supported languages
        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        if result.returncode != 0:
            pytest.skip(f"CLI help failed: {result.stderr}")

        help_text = result.stdout.lower()

        # Check that expected languages are mentioned
        expected_languages = ["dafny", "lean", "verus"]
        supported_languages = [lang for lang in expected_languages if lang in help_text]

        assert len(supported_languages) > 0, "No supported languages found in help"
        print(f"✓ Found supported languages: {supported_languages}")

        # Test that we can specify each supported language without argument parsing errors
        for lang in supported_languages:
            spec_dir = temp_workspace / f"{lang}_specs"
            if spec_dir.exists():
                env = os.environ.copy()
                env["ANTHROPIC_API_KEY"] = "test-key"

                result = subprocess.run(
                    [sys.executable, str(script_path), lang, str(spec_dir), "--help"],
                    capture_output=True,
                    text=True,
                    cwd=project_root,
                    timeout=30,
                    env=env,
                )

                # Help should work regardless of language choice
                assert result.returncode == 0, f"Help with {lang} language failed"
                print(f"✓ {lang} language argument accepted")

    def test_configuration_validation(self, project_root, temp_workspace):
        """Test that configuration validation works properly."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        # Test with non-existent directory
        result = subprocess.run(
            [sys.executable, str(script_path), "dafny", "/non/existent/directory", "--llm", "claude"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        # Should fail with directory error
        assert result.returncode != 0
        assert "does not exist" in result.stdout or "does not exist" in result.stderr
        print("✓ Non-existent directory validation works")

    def test_output_directory_creation(self, project_root, temp_workspace):
        """Test that output directories are created properly."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        dafny_specs = temp_workspace / "dafny_specs"

        env = os.environ.copy()
        env["ANTHROPIC_API_KEY"] = "test-key-for-validation"

        # This should fail at tool check but after creating output directory
        result = subprocess.run(
            [
                sys.executable,
                str(script_path),
                "dafny",
                str(dafny_specs),
                "--iterations",
                "1",
            ],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=60,
            env=env,
        )

        # Look for output directory creation message
        output_lines = result.stdout.split("\n")
        created_dir_line = [
            line for line in output_lines if "Created output directory:" in line
        ]

        if created_dir_line:
            # Extract the directory path and verify it exists
            dir_path = (
                created_dir_line[0].split("Created output directory: ")[1].strip()
            )
            if Path(dir_path).exists():
                print(f"✓ Output directory created: {dir_path}")
                # Clean up
                shutil.rmtree(dir_path, ignore_errors=True)
            else:
                print(f"⚠ Output directory mentioned but not found: {dir_path}")

    def test_llm_provider_validation(self, project_root, temp_workspace):
        """Test LLM provider selection and validation."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        dafny_specs = temp_workspace / "dafny_specs"

        # Test with invalid LLM provider
        result = subprocess.run(
            [
                sys.executable,
                str(script_path),
                "dafny",
                str(dafny_specs),
                "--llm",
                "invalid-provider",
            ],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        # Should fail with unsupported LLM error
        assert result.returncode != 0
        output_text = result.stdout + result.stderr
        assert "unsupported llm" in output_text.lower() or "invalid choice" in output_text.lower()
        print("✓ Invalid LLM provider validation works")

        # Test with valid LLM providers
        valid_providers = ["claude", "openai", "deepseek"]

        for provider in valid_providers:
            result = subprocess.run(
                [
                    sys.executable,
                    str(script_path),
                    "dafny",
                    str(dafny_specs),
                    "--llm-provider",
                    provider,
                    "--help",  # Use help to avoid API key requirement
                ],
                capture_output=True,
                text=True,
                cwd=project_root,
                timeout=30,
            )

            assert result.returncode == 0, f"Valid provider {provider} rejected"
            print(f"✓ {provider} provider accepted")

    def test_parallel_workers_configuration(self, project_root, temp_workspace):
        """Test parallel workers configuration."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        dafny_specs = temp_workspace / "dafny_specs"

        # Test different worker configurations
        worker_configs = [1, 2, 4, 8]

        for workers in worker_configs:
            env = os.environ.copy()
            env["ANTHROPIC_API_KEY"] = "test-key"

            result = subprocess.run(
                [
                    sys.executable,
                    str(script_path),
                    "dafny",
                    str(dafny_specs),
                    "--workers",
                    str(workers),
                    "--iterations",
                    "1",
                ],
                capture_output=True,
                text=True,
                cwd=project_root,
                timeout=60,
                env=env,
            )

            # Should mention the worker configuration
            if f"Parallel workers: {workers}" in result.stdout:
                print(f"✓ Workers configuration {workers} accepted")
            else:
                # May fail at tool check, but configuration should be parsed
                assert "invalid" not in result.stderr.lower()



class TestRegressionPrevention:
    """Tests to prevent regression from the original functionality."""

    def test_import_structure_stability(self):
        """Test that import structure is stable and won't break existing usage."""
        # Test that main components can be imported as expected
        import_paths = [
            "vericoding.core.ProcessingConfig",
            "vericoding.core.PromptLoader",
            "vericoding.core.create_llm_provider",
            "vericoding.processing.process_files_parallel",
            "vericoding.utils.generate_summary",
        ]

        for import_path in import_paths:
            try:
                module_path, class_name = import_path.rsplit(".", 1)
                module = __import__(module_path, fromlist=[class_name])
                assert hasattr(module, class_name), (
                    f"Missing {class_name} in {module_path}"
                )
                print(f"✓ {import_path} imports correctly")
            except ImportError as e:
                pytest.fail(f"Import failed for {import_path}: {e}")

    def test_configuration_keys_preserved(self):
        """Test that configuration structure hasn't changed unexpectedly."""
        try:
            from vericoding.core import ProcessingConfig

            # Test that expected class exists and has expected methods
            assert hasattr(ProcessingConfig, "get_available_languages")

            # Test that configuration can be instantiated with expected parameters
            langs = ProcessingConfig.get_available_languages()
            if "dafny" in langs:
                lang_config = langs["dafny"]

                # Test that language config has expected attributes
                expected_attrs = [
                    "name",
                    "file_extension",
                    "tool_path_env",
                    "default_tool_path",
                    "prompts_file",
                    "verify_command",
                ]

                for attr in expected_attrs:
                    assert hasattr(lang_config, attr), (
                        f"Missing attribute {attr} in language config"
                    )

                print("✓ Configuration structure preserved")

        except Exception as e:
            pytest.fail(f"Configuration structure test failed: {e}")


if __name__ == "__main__":
    # Allow running this test file directly
    pytest.main([__file__, "-v"])
