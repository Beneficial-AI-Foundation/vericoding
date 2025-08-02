"""Test basic package imports and module availability."""

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
)
from vericoding.processing import process_files_parallel
from vericoding.utils import generate_summary, generate_csv_results


class TestModularImports:
    """Test that all modular package imports work correctly."""

    def test_core_imports(self):
        """Test that core module imports work."""
        # These imports should not raise any exceptions
        assert load_environment is not None
        assert ProcessingConfig is not None
        assert PromptLoader is not None
        assert create_llm_provider is not None

    def test_language_tools_imports(self):
        """Test that language tools imports work."""
        assert get_tool_path is not None
        assert check_tool_availability is not None
        assert find_spec_files is not None

    def test_processing_imports(self):
        """Test that processing module imports work."""
        assert process_files_parallel is not None

    def test_utils_imports(self):
        """Test that utils module imports work."""
        assert generate_summary is not None
        assert generate_csv_results is not None

    def test_configuration_loading(self):
        """Test that configuration can be loaded successfully."""
        config = ProcessingConfig.get_available_languages()
        assert isinstance(config, dict)
        assert len(config) > 0
        print(f"Configuration loaded: {list(config.keys())}")
