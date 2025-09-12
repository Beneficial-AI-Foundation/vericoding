"""
Test to ensure vericoder.py provides equivalent functionality to the old monolithic version.
This test validates that the modular refactoring maintains all expected behaviors.
"""

import pytest
import subprocess
import sys
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock
import os

# Import the modular components
try:
    from vericoding.core import ProcessingConfig, PromptLoader, create_llm_provider
    from vericoding.core.language_tools import (
        get_tool_path,
        check_tool_availability,
        find_spec_files,
    )
    from vericoding.processing import process_files_parallel
    from vericoding.utils import generate_summary, generate_csv_results
except ImportError as e:
    pytest.skip(f"Cannot import modular components: {e}", allow_module_level=True)


class TestModularEquivalence:
    """Test that the modular version maintains all functionality of the original."""

    @pytest.fixture
    def project_root(self):
        """Get the project root directory."""
        return Path(__file__).parent.parent

    @pytest.fixture
    def temp_spec_directory(self):
        """Create a temporary directory with sample specification files."""
        temp_dir = tempfile.mkdtemp()
        temp_path = Path(temp_dir)

        # Create sample Dafny spec file
        dafny_spec = temp_path / "sample.dfy"
        dafny_spec.write_text("""
method Add(x: int, y: int) returns (sum: int)
    ensures sum == x + y
{
    // Implementation needed
}
""")

        # Create sample Lean spec file
        lean_spec = temp_path / "sample.lean"
        lean_spec.write_text("""
def add (x y : ℕ) : ℕ := sorry
""")

        yield temp_path
        shutil.rmtree(temp_dir, ignore_errors=True)

    def test_cli_arguments_parsing(self, project_root):
        """Test that CLI argument parsing works correctly."""
        script_path = project_root / "vericoder.py"

        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        # Test help command works
        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        assert result.returncode == 0, f"Help command failed: {result.stderr}"
        assert "Unified Specification-to-Code Processing" in result.stdout
        assert (
            "dafny" in result.stdout
            or "lean" in result.stdout
            or "verus" in result.stdout
        )

    def test_configuration_setup_consistency(self):
        """Test that configuration setup produces expected structure."""

        # Mock command line arguments
        class MockArgs:
            language = "dafny"
            folder = Path("/tmp/test")
            iterations = 5
            debug = False
            strict_specs = False
            workers = 4
            api_rate_limit_delay = 1
            max_directory_traversal_depth = 50
            llm_provider = "claude"
            llm_model = None

        # This would normally require actual directory setup, so we'll mock it
        with (
            patch("pathlib.Path.is_dir", return_value=True),
            patch("pathlib.Path.mkdir"),
            patch.object(ProcessingConfig, "get_available_languages") as mock_langs,
        ):
            # Mock available languages
            from vericoding.core.config import LanguageConfig

            mock_langs.return_value = {
                "dafny": LanguageConfig(
                    name="Dafny",
                    file_extension=".dfy",
                    tool_path_env="DAFNY_PATH",
                    default_tool_path="dafny",
                    prompts_file="prompts.yaml",
                    verify_command=["dafny", "verify"],
                    compile_check_command=["dafny", "build"],
                    code_block_patterns=["dafny"],
                    keywords=["method", "function", "predicate"],
                    spec_patterns=[r"ensures.*", r"requires.*"],
                )
            }

            # Test that we can create configuration without errors
            try:
                # This imports from the modular script directly
                sys.path.insert(0, str(Path(__file__).parent.parent))
                from vericoder import setup_configuration

                args = MockArgs()
                config = setup_configuration(args)

                assert config.language == "dafny"
                assert config.max_iterations == 5
                assert config.max_workers == 4
                assert config.llm_provider == "claude"

            except Exception as e:
                pytest.fail(f"Configuration setup failed: {e}")
            finally:
                if str(Path(__file__).parent.parent) in sys.path:
                    sys.path.remove(str(Path(__file__).parent.parent))

    def test_component_integration(self):
        """Test that modular components integrate correctly."""
        # Test ProcessingConfig can be created
        try:
            available_langs = ProcessingConfig.get_available_languages()
            assert isinstance(available_langs, dict)
            assert len(available_langs) > 0
            print(f"✓ Found {len(available_langs)} available languages")
        except Exception as e:
            pytest.fail(f"ProcessingConfig.get_available_languages() failed: {e}")

        # Test PromptLoader can be instantiated (with mocked file)
        with (
            patch("pathlib.Path.exists", return_value=True),
            patch("builtins.open", create=True) as mock_open,
        ):
            mock_open.return_value.__enter__.return_value.read.return_value = """
generate_code: "Generate code from specification"  
fix_verification: "Fix verification errors"
"""

            try:
                loader = PromptLoader("dafny", "prompts.yaml")
                validation = loader.validate_prompts()
                assert validation.valid or len(validation.missing) == 0
                print("✓ PromptLoader integration works")
            except Exception as e:
                pytest.fail(f"PromptLoader integration failed: {e}")

    def test_llm_provider_creation(self):
        """Test that LLM provider creation works as expected."""
        # Test with mock API key
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}):
            try:
                provider = create_llm_provider("claude")
                assert provider is not None
                assert provider.model == "claude-sonnet-4-20250514"  # default model
                print("✓ LLM provider creation works")
            except Exception as e:
                pytest.fail(f"LLM provider creation failed: {e}")

        # Test with custom model
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"}):
            try:
                provider = create_llm_provider("claude", "claude-3-5-haiku-20241022")
                assert provider.model == "claude-3-5-haiku-20241022"
                print("✓ Custom model selection works")
            except Exception as e:
                pytest.fail(f"Custom model selection failed: {e}")

    @pytest.mark.skip(reason="Requires actual tool installation")
    def test_tool_availability_check(self, temp_spec_directory):
        """Test tool availability checking."""
        # This test would require actual Dafny/Lean/Verus installation
        # Skipped by default but can be enabled for integration testing
        pass

    def test_file_finding_logic(self, temp_spec_directory):
        """Test that file finding works correctly."""

        # Mock configuration for file finding
        class MockConfig:
            files_dir = str(temp_spec_directory)
            language = "dafny"
            language_config = type(
                "MockLangConfig",
                (),
                {"file_extension": ".dfy", "keywords": ["method", "function"]},
            )()

        config = MockConfig()

        try:
            files = find_spec_files(config)
            assert len(files) >= 1  # Should find the .dfy file we created
            assert any(f.endswith(".dfy") for f in files)
            print(f"✓ Found {len(files)} specification files")
        except Exception as e:
            pytest.fail(f"File finding failed: {e}")

    def test_output_generation_structure(self):
        """Test that output generation maintains expected structure."""
        # Mock results for testing
        from vericoding.processing.file_processor import ProcessingResult

        mock_results = [
            ProcessingResult(
                success=True,
                file="test1.dfy",
                output="success",
                error=None,
                has_bypass=False,
            ),
            ProcessingResult(
                success=False,
                file="test2.dfy",
                output=None,
                error="verification failed",
                has_bypass=False,
            ),
        ]

        # Mock configuration
        class MockConfig:
            language_config = type(
                "MockLangConfig", (), {"name": "Dafny", "file_extension": ".dfy"}
            )()
            files_dir = "/tmp/test"
            output_dir = "/tmp/output"
            max_iterations = 5
            max_workers = 4
            summary_file = "/tmp/output/summary.txt"
            debug_mode = False
            strict_spec_verification = False
            llm_provider = "claude"
            llm_model = "claude-3-5-sonnet-20241022"
            api_rate_limit_delay = 1

        config = MockConfig()

        with (
            patch("builtins.open", create=True),
            patch("pathlib.Path.open", create=True),
        ):
            try:
                summary = generate_summary(config, mock_results)
                assert "DAFNY SPECIFICATION-TO-CODE PROCESSING SUMMARY" in summary
                assert "Total successful: 1" in summary
                assert "Total failed: 1" in summary
                print("✓ Summary generation works")
            except Exception as e:
                pytest.fail(f"Summary generation failed: {e}")

    def test_modular_imports_work(self):
        """Test that all modular imports resolve correctly."""
        import_tests = [
            (
                "vericoding.core",
                ["ProcessingConfig", "PromptLoader", "create_llm_provider"],
            ),
            (
                "vericoding.core.language_tools",
                ["get_tool_path", "check_tool_availability", "find_spec_files"],
            ),
            ("vericoding.processing", ["process_files_parallel"]),
            ("vericoding.utils", ["generate_summary", "generate_csv_results"]),
        ]

        for module_name, expected_items in import_tests:
            try:
                module = __import__(module_name, fromlist=expected_items)
                for item in expected_items:
                    assert hasattr(module, item), f"{module_name} missing {item}"
                print(f"✓ {module_name} imports correctly")
            except ImportError as e:
                pytest.fail(f"Failed to import {module_name}: {e}")

    def test_backwards_compatibility_scenarios(self):
        """Test scenarios that were supported in the original version."""
        scenarios = [
            # Test different language configurations
            {"language": "dafny", "expected_extension": ".dfy"},
            {"language": "lean", "expected_extension": ".lean"},
            {"language": "verus", "expected_extension": ".rs"},
        ]

        try:
            available_langs = ProcessingConfig.get_available_languages()

            for scenario in scenarios:
                lang = scenario["language"]
                if lang in available_langs:
                    lang_config = available_langs[lang]
                    assert lang_config.file_extension == scenario["expected_extension"]
                    print(f"✓ {lang} configuration is correct")
                else:
                    print(f"⚠ {lang} not available in current configuration")

        except Exception as e:
            pytest.fail(f"Backwards compatibility test failed: {e}")


class TestFunctionalEquivalence:
    """Test functional equivalence between old and new implementations."""

    def test_same_cli_interface(self, project_root):
        """Test that the CLI interface signature hasn't changed."""
        script_path = project_root / "vericoder.py"
        if not script_path.exists():
            pytest.skip("vericoder.py not found")

        # Get help output
        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )

        if result.returncode != 0:
            pytest.skip(f"CLI help failed: {result.stderr}")

        help_text = result.stdout

        # Check that all expected arguments are present
        expected_args = [
            "--iterations",
            "-i",
            "--debug",
            "--strict-specs",
            "--workers",
            "-w",
            "--api-rate-limit-delay",
            "--llm-provider",
            "--llm-model",
        ]

        for arg in expected_args:
            assert arg in help_text, f"Missing CLI argument: {arg}"

        print(f"✓ All expected CLI arguments present")

    @pytest.fixture
    def project_root(self):
        """Get the project root directory."""
        return Path(__file__).parent.parent


if __name__ == "__main__":
    # Allow running this test file directly
    pytest.main([__file__, "-v"])
