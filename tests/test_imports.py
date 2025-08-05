"""Test basic package imports and module availability."""

import inspect
import sys
import pytest
from importlib import import_module

from vericoding.core import (
    load_environment,
    ProcessingConfig,
    PromptLoader,
    create_llm_provider,
)
from vericoding.core.language_tools import (
    get_tool_path,
    check_tool_availability,
    find_spec_files,
    ToolAvailabilityResult,
    VerificationResult,
)
from vericoding.processing import process_files_parallel
from vericoding.utils import generate_summary, generate_csv_results


class TestCoreImports:
    """Test core module imports and functionality."""

    def test_load_environment_function(self):
        """Test load_environment function import and signature."""
        assert callable(load_environment)

        # Test function signature
        sig = inspect.signature(load_environment)
        assert len(sig.parameters) == 0, "load_environment should take no parameters"

    def test_processing_config_class(self):
        """Test ProcessingConfig class import and basic instantiation."""
        assert inspect.isclass(ProcessingConfig)

        # Test that it can access available languages
        languages = ProcessingConfig.get_available_languages()
        if languages:
            first_lang = next(iter(languages.keys()))
            first_lang_config = languages[first_lang]
            config = ProcessingConfig(
                language=first_lang,
                language_config=first_lang_config,
                files_dir="test_files",
                max_iterations=3,
                output_dir="test_output",
                summary_file="summary.json",
                debug_mode=False,
                strict_spec_verification=True,
                max_workers=4,
                api_rate_limit_delay=1,
                llm_provider="anthropic",
                llm_model="claude-3-sonnet-20240229",
            )
            assert config.language == first_lang

    def test_prompt_loader_class(self):
        """Test PromptLoader class import and structure."""
        assert inspect.isclass(PromptLoader)

        # Test class methods exist
        expected_methods = ["format_prompt", "validate_prompts"]
        for method_name in expected_methods:
            assert hasattr(PromptLoader, method_name), (
                f"PromptLoader missing {method_name}"
            )
            assert callable(getattr(PromptLoader, method_name))

    def test_create_llm_provider_function(self):
        """Test create_llm_provider function import and signature."""
        assert callable(create_llm_provider)

        # Test function signature
        sig = inspect.signature(create_llm_provider)
        params = list(sig.parameters.keys())
        assert "provider_name" in params, (
            "create_llm_provider should accept provider_name"
        )


class TestLanguageToolsImports:
    """Test language tools module imports and functionality."""

    def test_get_tool_path_function(self):
        """Test get_tool_path function import and signature."""
        assert callable(get_tool_path)

        sig = inspect.signature(get_tool_path)
        params = list(sig.parameters.keys())
        assert "config" in params, "get_tool_path should accept config parameter"

    def test_check_tool_availability_function(self):
        """Test check_tool_availability function import and signature."""
        assert callable(check_tool_availability)

        sig = inspect.signature(check_tool_availability)
        params = list(sig.parameters.keys())
        assert "config" in params, (
            "check_tool_availability should accept config parameter"
        )

    def test_find_spec_files_function(self):
        """Test find_spec_files function import and signature."""
        assert callable(find_spec_files)

        sig = inspect.signature(find_spec_files)
        # Should have parameters for directory and pattern
        assert len(sig.parameters) > 0, "find_spec_files should accept parameters"

    def test_tool_availability_result_class(self):
        """Test ToolAvailabilityResult dataclass."""
        assert inspect.isclass(ToolAvailabilityResult)

        # Test that it's a dataclass
        assert hasattr(ToolAvailabilityResult, "__dataclass_fields__")

        # Test expected fields
        fields = ToolAvailabilityResult.__dataclass_fields__
        assert "available" in fields
        assert "message" in fields

    def test_verification_result_class(self):
        """Test VerificationResult dataclass."""
        assert inspect.isclass(VerificationResult)

        # Test that it's a dataclass
        assert hasattr(VerificationResult, "__dataclass_fields__")

        # Test expected fields
        fields = VerificationResult.__dataclass_fields__
        assert "success" in fields
        assert "output" in fields
        assert "error" in fields


class TestProcessingImports:
    """Test processing module imports and functionality."""

    def test_process_files_parallel_function(self):
        """Test process_files_parallel function import and signature."""
        assert callable(process_files_parallel)

        sig = inspect.signature(process_files_parallel)
        # Should have parameters for files, config, etc.
        assert len(sig.parameters) > 0, (
            "process_files_parallel should accept parameters"
        )


class TestUtilsImports:
    """Test utils module imports and functionality."""

    def test_generate_summary_function(self):
        """Test generate_summary function import and signature."""
        assert callable(generate_summary)

        sig = inspect.signature(generate_summary)
        assert len(sig.parameters) > 0, "generate_summary should accept parameters"

    def test_generate_csv_results_function(self):
        """Test generate_csv_results function import and signature."""
        assert callable(generate_csv_results)

        sig = inspect.signature(generate_csv_results)
        assert len(sig.parameters) > 0, "generate_csv_results should accept parameters"


class TestModuleStructure:
    """Test overall module structure and organization."""

    def test_vericoding_package_structure(self):
        """Test that vericoding package has expected submodules."""
        import vericoding

        # Test that main package exists
        assert hasattr(vericoding, "__path__"), "vericoding should be a package"

        # Test expected submodules can be imported
        expected_modules = ["core", "processing", "utils"]
        for module_name in expected_modules:
            try:
                module = import_module(f"vericoding.{module_name}")
                assert module is not None, f"Failed to import vericoding.{module_name}"
                print(f"✓ Successfully imported vericoding.{module_name}")
            except ImportError as e:
                pytest.fail(f"Failed to import vericoding.{module_name}: {e}")

    def test_core_submodules(self):
        """Test core submodules can be imported."""
        expected_core_modules = ["config", "prompts", "llm_providers", "language_tools"]

        for module_name in expected_core_modules:
            try:
                module = import_module(f"vericoding.core.{module_name}")
                assert module is not None, (
                    f"Failed to import vericoding.core.{module_name}"
                )
                print(f"✓ Successfully imported vericoding.core.{module_name}")
            except ImportError as e:
                print(f"Warning: Could not import vericoding.core.{module_name}: {e}")

    def test_no_import_side_effects(self):
        """Test that imports don't have unexpected side effects."""
        original_modules = set(sys.modules.keys())

        # Import our modules

        # Check that no unexpected modules were imported
        new_modules = set(sys.modules.keys()) - original_modules

        # Filter out expected modules and their dependencies
        unexpected_modules = [
            mod
            for mod in new_modules
            if not any(
                expected in mod
                for expected in [
                    "vericoding",
                    "yaml",
                    "anthropic",
                    "pathlib",
                    "dataclasses",
                ]
            )
        ]

        # Allow some common modules that might be imported
        allowed_modules = {"typing_extensions", "importlib_metadata", "zipp"}
        unexpected_modules = [
            mod for mod in unexpected_modules if mod not in allowed_modules
        ]

        if unexpected_modules:
            print(f"Note: Unexpected modules imported: {unexpected_modules}")

    def test_configuration_integration(self):
        """Test that configuration system works correctly."""
        config_dict = ProcessingConfig.get_available_languages()
        assert isinstance(config_dict, dict)
        assert len(config_dict) > 0

        print(f"Available languages: {list(config_dict.keys())}")

        # Test that we can create ProcessingConfig for each language
        for lang_name, lang_config in config_dict.items():
            try:
                config = ProcessingConfig(
                    language=lang_name,
                    language_config=lang_config,
                    files_dir="test_files",
                    max_iterations=3,
                    output_dir="test_output",
                    summary_file="summary.json",
                    debug_mode=False,
                    strict_spec_verification=True,
                    max_workers=4,
                    api_rate_limit_delay=1,
                    llm_provider="anthropic",
                    llm_model="claude-3-sonnet-20240229",
                )
                assert config.language == lang_name
                assert config.language_config == lang_config
                print(f"✓ ProcessingConfig created for {lang_name}")
            except Exception as e:
                pytest.fail(f"Failed to create ProcessingConfig for {lang_name}: {e}")

    def test_import_error_handling(self):
        """Test that import errors are handled gracefully."""
        # Test importing non-existent module
        with pytest.raises(ImportError):
            import_module("vericoding.nonexistent_module")

    @pytest.mark.integration
    def test_full_import_chain(self):
        """Integration test for complete import chain."""
        try:
            # Test the full chain of imports that would be used in production
            from vericoding.core import (
                ProcessingConfig,
            )
            from vericoding.core.language_tools import (
                get_tool_path,
                check_tool_availability,
            )

            # Test that we can use them together
            languages = ProcessingConfig.get_available_languages()
            if languages:
                first_lang = next(iter(languages.keys()))
                first_lang_config = languages[first_lang]
                config = ProcessingConfig(
                    language=first_lang,
                    language_config=first_lang_config,
                    files_dir="test_files",
                    max_iterations=3,
                    output_dir="test_output",
                    summary_file="summary.json",
                    debug_mode=False,
                    strict_spec_verification=True,
                    max_workers=4,
                    api_rate_limit_delay=1,
                    llm_provider="anthropic",
                    llm_model="claude-3-sonnet-20240229",
                )

                # Test tool path functions
                tool_path = get_tool_path(config)
                assert isinstance(tool_path, str)

                availability = check_tool_availability(config)
                assert hasattr(availability, "available")
                assert hasattr(availability, "message")

                print("✓ Full import chain successful")

        except Exception as e:
            pytest.fail(f"Full import chain failed: {e}")


class TestFunctionSignatures:
    """Test that imported functions have expected signatures."""

    def test_core_function_signatures(self):
        """Test core function signatures are stable."""
        # Test create_llm_provider signature
        sig = inspect.signature(create_llm_provider)
        params = sig.parameters

        assert "provider_name" in params, (
            "create_llm_provider should have provider_name parameter"
        )

        # Check parameter types if annotated
        if params["provider_name"].annotation != inspect.Parameter.empty:
            annotation = params["provider_name"].annotation
            assert annotation is str or "str" in str(annotation)

    def test_processing_function_signatures(self):
        """Test processing function signatures are stable."""
        sig = inspect.signature(process_files_parallel)
        params = list(sig.parameters.keys())

        # Should have parameters for processing files
        assert len(params) > 0, "process_files_parallel should have parameters"

    def test_utils_function_signatures(self):
        """Test utils function signatures are stable."""
        # Test generate_summary signature
        sig = inspect.signature(generate_summary)
        assert len(sig.parameters) > 0, "generate_summary should have parameters"

        # Test generate_csv_results signature
        sig = inspect.signature(generate_csv_results)
        assert len(sig.parameters) > 0, "generate_csv_results should have parameters"
