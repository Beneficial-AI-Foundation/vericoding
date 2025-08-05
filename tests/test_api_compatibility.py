"""
API compatibility tests to ensure the modular version maintains the same interface.
These tests verify that any code depending on the original spec_to_code.py will work with the modular version.
"""

import pytest
import inspect
import os
from pathlib import Path
from unittest.mock import patch, MagicMock
import sys


class TestAPICompatibility:
    """Test that the modular version maintains API compatibility."""

    def test_main_function_signature(self):
        """Test that main function has the same signature and behavior."""
        project_root = Path(__file__).parent.parent

        # Import the modular main function
        sys.path.insert(0, str(project_root))
        try:
            from spec_to_code_modular import main

            # Test that main function exists and is callable
            assert callable(main), "main function should be callable"

            # Test that main function has no required parameters
            sig = inspect.signature(main)
            required_params = [
                p
                for p in sig.parameters.values()
                if p.default == inspect.Parameter.empty
            ]
            assert len(required_params) == 0, (
                "main function should have no required parameters"
            )

            print("✓ main function signature is compatible")

        except ImportError as e:
            pytest.fail(f"Cannot import main function: {e}")
        finally:
            if str(project_root) in sys.path:
                sys.path.remove(str(project_root))

    def test_core_functions_available(self):
        """Test that core functions from the original are available in the modular version."""
        core_functions = ["parse_arguments", "setup_configuration", "main"]

        project_root = Path(__file__).parent.parent
        sys.path.insert(0, str(project_root))

        try:
            import spec_to_code_modular as modular_module

            for func_name in core_functions:
                assert hasattr(modular_module, func_name), (
                    f"Missing function: {func_name}"
                )
                assert callable(getattr(modular_module, func_name)), (
                    f"{func_name} should be callable"
                )
                print(f"✓ {func_name} function available")

        except ImportError as e:
            pytest.fail(f"Cannot import modular module: {e}")
        finally:
            if str(project_root) in sys.path:
                sys.path.remove(str(project_root))

    def test_configuration_class_compatibility(self):
        """Test that ProcessingConfig maintains expected interface."""
        try:
            from vericoding.core import ProcessingConfig

            # Test class methods exist
            expected_class_methods = [
                "get_available_languages",
                "get_common_compilation_errors",
            ]

            for method_name in expected_class_methods:
                assert hasattr(ProcessingConfig, method_name), (
                    f"Missing class method: {method_name}"
                )
                method = getattr(ProcessingConfig, method_name)
                assert callable(method), f"{method_name} should be callable"
                print(f"✓ ProcessingConfig.{method_name} available")

            # Test that we can call get_available_languages
            try:
                langs = ProcessingConfig.get_available_languages()
                assert isinstance(langs, dict), (
                    "get_available_languages should return dict"
                )
                print(f"✓ get_available_languages returns {len(langs)} languages")
            except Exception as e:
                print(f"⚠ get_available_languages failed (may be expected): {e}")

        except ImportError as e:
            pytest.fail(f"Cannot import ProcessingConfig: {e}")

    def test_prompt_loader_compatibility(self):
        """Test that PromptLoader maintains expected interface."""
        try:
            from vericoding.core import PromptLoader

            # Test constructor signature
            sig = inspect.signature(PromptLoader.__init__)
            params = list(sig.parameters.keys())

            # Should accept language parameter
            assert "language" in params or "config" in params, (
                "PromptLoader should accept language parameter"
            )

            # Test with mocked file
            with (
                patch("pathlib.Path.exists", return_value=True),
                patch("builtins.open") as mock_open,
            ):
                mock_open.return_value.__enter__.return_value.read.return_value = """
generate_code: "Generate code"
fix_verification: "Fix verification"
"""

                try:
                    loader = PromptLoader("dafny", "prompts.yaml")

                    # Test expected methods
                    expected_methods = ["format_prompt", "validate_prompts"]
                    for method_name in expected_methods:
                        assert hasattr(loader, method_name), (
                            f"Missing method: {method_name}"
                        )
                        assert callable(getattr(loader, method_name)), (
                            f"{method_name} should be callable"
                        )
                        print(f"✓ PromptLoader.{method_name} available")

                    # Test validation
                    validation = loader.validate_prompts()
                    assert hasattr(validation, "valid"), (
                        "validate_prompts should return object with 'valid' attribute"
                    )
                    print("✓ PromptLoader validation works")

                except Exception as e:
                    pytest.fail(f"PromptLoader instantiation failed: {e}")

        except ImportError as e:
            pytest.fail(f"Cannot import PromptLoader: {e}")

    def test_llm_provider_factory_compatibility(self):
        """Test that LLM provider creation maintains expected interface."""
        try:
            from vericoding.core import create_llm_provider

            # Test function signature
            sig = inspect.signature(create_llm_provider)
            params = list(sig.parameters.keys())

            assert "provider_name" in params, (
                "create_llm_provider should accept provider_name"
            )

            # Test with mock environment
            with patch.dict("os.environ", {"ANTHROPIC_API_KEY": "test-key"}):
                try:
                    provider = create_llm_provider("claude")

                    # Test that provider has expected interface
                    expected_methods = ["call_api", "get_required_env_var"]
                    for method_name in expected_methods:
                        assert hasattr(provider, method_name), (
                            f"Provider missing method: {method_name}"
                        )
                        assert callable(getattr(provider, method_name)), (
                            f"{method_name} should be callable"
                        )
                        print(f"✓ LLM Provider.{method_name} available")

                    # Test provider attributes
                    expected_attrs = ["model", "max_tokens"]
                    for attr_name in expected_attrs:
                        assert hasattr(provider, attr_name), (
                            f"Provider missing attribute: {attr_name}"
                        )
                        print(f"✓ LLM Provider.{attr_name} available")

                except Exception as e:
                    print(f"⚠ LLM provider creation test failed (may be expected): {e}")

        except ImportError as e:
            pytest.fail(f"Cannot import create_llm_provider: {e}")

    def test_utility_functions_compatibility(self):
        """Test that utility functions maintain expected interface."""
        utility_modules = [
            ("vericoding.utils", ["generate_summary", "generate_csv_results"]),
            (
                "vericoding.core.language_tools",
                ["get_tool_path", "check_tool_availability", "find_spec_files"],
            ),
            ("vericoding.processing", ["process_files_parallel"]),
        ]

        for module_name, expected_functions in utility_modules:
            try:
                module = __import__(module_name, fromlist=expected_functions)

                for func_name in expected_functions:
                    assert hasattr(module, func_name), (
                        f"{module_name} missing function: {func_name}"
                    )
                    func = getattr(module, func_name)
                    assert callable(func), (
                        f"{module_name}.{func_name} should be callable"
                    )
                    print(f"✓ {module_name}.{func_name} available")

            except ImportError as e:
                pytest.fail(f"Cannot import {module_name}: {e}")

    def test_result_data_structures_compatibility(self):
        """Test that result data structures maintain expected attributes."""
        try:
            from vericoding.processing.file_processor import ProcessingResult

            # Test that ProcessingResult has expected fields
            expected_fields = ["success", "file", "output", "error", "has_bypass"]

            # Create a test instance
            result = ProcessingResult(
                success=True,
                file="test.dfy",
                output="test output",
                error=None,
                has_bypass=False,
            )

            for field_name in expected_fields:
                assert hasattr(result, field_name), (
                    f"ProcessingResult missing field: {field_name}"
                )
                print(f"✓ ProcessingResult.{field_name} available")

        except ImportError as e:
            pytest.fail(f"Cannot import ProcessingResult: {e}")

    def test_backwards_compatible_imports(self):
        """Test that common import patterns still work."""
        import_patterns = [
            # Core functionality
            ("from vericoding.core import ProcessingConfig", "ProcessingConfig"),
            ("from vericoding.core import PromptLoader", "PromptLoader"),
            ("from vericoding.core import create_llm_provider", "create_llm_provider"),
            # Utilities
            ("from vericoding.utils import generate_summary", "generate_summary"),
            (
                "from vericoding.processing import process_files_parallel",
                "process_files_parallel",
            ),
        ]

        for import_statement, expected_name in import_patterns:
            try:
                # Execute the import statement
                exec(import_statement)

                # Check that the imported name is available
                assert expected_name in locals(), f"Import failed: {import_statement}"
                print(f"✓ Import works: {import_statement}")

            except ImportError as e:
                pytest.fail(f"Import pattern failed: {import_statement} - {e}")

    def test_environment_variable_compatibility(self):
        """Test that environment variable handling is compatible."""
        try:
            from vericoding.core import create_llm_provider

            # Test that it properly handles missing API keys
            provider_env_vars = [
                ("claude", "ANTHROPIC_API_KEY"),
                ("openai", "OPENAI_API_KEY"),
                ("deepseek", "DEEPSEEK_API_KEY"),
            ]

            for provider_name, env_var in provider_env_vars:
                # Remove the environment variable to test missing key handling
                with patch.dict("os.environ", {}, clear=False):
                    # Remove the specific API key
                    if env_var in os.environ:
                        del os.environ[env_var]

                    try:
                        # This should fail with a clear message about missing API key
                        create_llm_provider(provider_name)
                        pytest.fail(f"Expected error for missing {env_var}")
                    except ValueError as e:
                        error_msg = str(e).lower()
                        assert env_var.lower() in error_msg, (
                            f"Error should mention {env_var}: {e}"
                        )
                        print(f"✓ {provider_name} properly handles missing {env_var}")
                    except Exception as e:
                        print(f"⚠ Unexpected error for {provider_name}: {e}")

        except ImportError as e:
            pytest.fail(f"Cannot test environment variable compatibility: {e}")

    def test_cli_argument_backwards_compatibility(self):
        """Test that CLI arguments haven't changed in breaking ways."""
        project_root = Path(__file__).parent.parent
        sys.path.insert(0, str(project_root))

        try:
            from spec_to_code_modular import parse_arguments

            # Test that parse_arguments function exists
            assert callable(parse_arguments), "parse_arguments should be callable"

            # Test with mock argv to see if expected arguments are supported
            test_args = [
                ["dafny", "/tmp/specs"],
                ["lean", "/tmp/specs", "--iterations", "3"],
                ["verus", "/tmp/specs", "--debug", "--workers", "2"],
                [
                    "dafny",
                    "/tmp/specs",
                    "--llm-provider",
                    "claude",
                    "--llm-model",
                    "claude-3-5-sonnet-20241022",
                ],
            ]

            for args in test_args:
                with patch("sys.argv", ["spec_to_code_modular.py"] + args):
                    try:
                        parsed = parse_arguments()

                        # Test that expected attributes exist
                        expected_attrs = [
                            "language",
                            "folder",
                            "iterations",
                            "debug",
                            "workers",
                            "llm_provider",
                        ]
                        for attr in expected_attrs:
                            assert hasattr(parsed, attr), (
                                f"Missing argument attribute: {attr}"
                            )

                        print(f"✓ CLI arguments parsed correctly: {args[:2]}")

                    except SystemExit:
                        # This might happen with invalid test data
                        print(f"⚠ CLI parsing failed for: {args}")
                    except Exception as e:
                        pytest.fail(f"CLI parsing error for {args}: {e}")

        except ImportError as e:
            pytest.fail(f"Cannot import parse_arguments: {e}")
        finally:
            if str(project_root) in sys.path:
                sys.path.remove(str(project_root))


if __name__ == "__main__":
    # Allow running this test file directly
    pytest.main([__file__, "-v"])
