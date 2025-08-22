"""Test prompt loading functionality."""

import pytest
from unittest.mock import patch
import yaml

from vericoding.core.prompts import PromptLoader, PromptValidationResult
from vericoding.core.config import ProcessingConfig


class TestPromptLoader:
    """Test prompt loading system with comprehensive scenarios."""

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_prompt_loader_with_valid_yaml(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test PromptLoader with a valid YAML file."""
        test_prompts = {
            "generate_code": "Generate code for: {spec}",
            "fix_verification": "Fix verification errors in: {code}",
            "custom_prompt": "Custom prompt with {param1} and {param2}",
        }

        # Setup mocks
        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang", "prompts.yaml")

        # Test that prompts were loaded correctly
        assert loader.prompts == test_prompts
        assert loader.language == "test_lang"
        assert loader.prompts_file == "prompts.yaml"

    @patch("vericoding.core.prompts.Path.exists")
    def test_prompt_loader_file_not_found(self, mock_exists):
        """Test PromptLoader behavior when prompts file doesn't exist."""
        mock_exists.return_value = False

        with pytest.raises(FileNotFoundError, match="Prompts file not found"):
            PromptLoader("test_lang", "nonexistent.yaml")

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_prompt_loader_invalid_yaml(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test PromptLoader behavior with invalid YAML."""
        mock_exists.return_value = True
        mock_yaml_load.side_effect = yaml.YAMLError("Invalid YAML")

        with pytest.raises(yaml.YAMLError):
            PromptLoader("test_lang", "invalid.yaml")

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_format_prompt_success(self, mock_exists, mock_open_method, mock_yaml_load):
        """Test successful prompt formatting with parameters."""
        test_prompts = {
            "test_prompt": "Hello {name}, you have {count} messages",
            "simple_prompt": "Simple prompt without parameters",
        }

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")

        # Test formatting with parameters
        result = loader.format_prompt("test_prompt", name="Alice", count=5)
        assert result == "Hello Alice, you have 5 messages"

        # Test formatting without parameters
        result = loader.format_prompt("simple_prompt")
        assert result == "Simple prompt without parameters"

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_format_prompt_missing_prompt(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test format_prompt with non-existent prompt name."""
        test_prompts = {"existing_prompt": "This exists"}

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")

        with pytest.raises(KeyError, match="Prompt 'missing_prompt' not found"):
            loader.format_prompt("missing_prompt")

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_format_prompt_missing_placeholder(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test format_prompt with missing placeholder parameters."""
        test_prompts = {"test_prompt": "Hello {name}, you have {count} messages"}

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")

        with pytest.raises(
            KeyError, match="Missing placeholder in prompt 'test_prompt'"
        ):
            loader.format_prompt("test_prompt", name="Alice")  # Missing 'count'

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_format_prompt_formatting_error(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test format_prompt with invalid formatting."""
        test_prompts = {"bad_prompt": "Invalid format {"}

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")

        with pytest.raises(ValueError, match="Error formatting prompt 'bad_prompt'"):
            loader.format_prompt("bad_prompt")

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_validate_prompts_all_required_present(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test validate_prompts when all required prompts are present."""
        test_prompts = {
            "generate_code": "Generate code prompt",
            "fix_verification": "Fix verification prompt",
            "extra_prompt": "Additional prompt",
        }

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")
        result = loader.validate_prompts()

        assert isinstance(result, PromptValidationResult)
        assert result.valid is True
        assert result.missing == []
        assert set(result.available) == {
            "generate_code",
            "fix_verification",
            "extra_prompt",
        }

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_validate_prompts_partial_prompts(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test validate_prompts with some missing prompts."""
        test_prompts = {"generate_code": "Generate code"}

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")
        result = loader.validate_prompts()

        assert isinstance(result, PromptValidationResult)
        assert result.valid is False
        assert result.missing == ["fix_verification"]
        assert result.available == ["generate_code"]

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_validate_prompts_empty_prompts(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test validate_prompts with empty prompts file."""
        test_prompts = {}

        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang")
        result = loader.validate_prompts()

        assert isinstance(result, PromptValidationResult)
        assert result.valid is False
        assert set(result.missing) == {"generate_code", "fix_verification"}
        assert result.available == []

    @patch("vericoding.core.prompts.yaml.safe_load")
    @patch("vericoding.core.prompts.Path.open")
    @patch("vericoding.core.prompts.Path.exists")
    def test_prompt_loader_file_path_resolution(
        self, mock_exists, mock_open_method, mock_yaml_load
    ):
        """Test that PromptLoader correctly resolves file paths."""
        test_prompts = {"test": "prompt"}

        # Test language-specific directory path
        mock_exists.return_value = True
        mock_yaml_load.return_value = test_prompts

        loader = PromptLoader("test_lang", "prompts.yaml")
        assert loader.prompts == test_prompts

    def test_prompt_validation_result_dataclass(self):
        """Test PromptValidationResult dataclass functionality."""
        result = PromptValidationResult(
            valid=True, missing=["prompt1"], available=["prompt2", "prompt3"]
        )

        assert result.valid is True
        assert result.missing == ["prompt1"]
        assert result.available == ["prompt2", "prompt3"]

    @pytest.mark.integration
    def test_prompt_loader_with_real_files(self):
        """Integration test with actual prompt files if they exist."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
            try:
                loader = PromptLoader(lang_name, lang_config.prompts_file)

                # Test that prompts were loaded
                assert isinstance(loader.prompts, dict)

                # Test validation
                validation = loader.validate_prompts()
                assert isinstance(validation, PromptValidationResult)

                # If valid, test formatting with dummy parameters
                if validation.valid and "generate_code" in loader.prompts:
                    try:
                        # Try formatting with common parameters
                        formatted = loader.format_prompt(
                            "generate_code", spec="test spec"
                        )
                        assert isinstance(formatted, str)
                        assert len(formatted) > 0
                    except (KeyError, ValueError):
                        # Expected if prompt requires different parameters
                        pass

                print(f"✓ {lang_name}: prompts loaded successfully")

            except FileNotFoundError:
                print(
                    f"Note: {lang_name} prompts file not found (expected in test environment)"
                )
            except Exception as e:
                pytest.fail(f"Unexpected error loading {lang_name} prompts: {e}")


class TestPromptValidationResult:
    """Test PromptValidationResult dataclass."""

    def test_validation_result_creation(self):
        """Test creating PromptValidationResult instances."""
        result = PromptValidationResult(True, [], ["p1", "p2"])
        assert result.valid is True
        assert result.missing == []
        assert result.available == ["p1", "p2"]

    def test_validation_result_equality(self):
        """Test PromptValidationResult equality comparison."""
        result1 = PromptValidationResult(True, [], ["p1"])
        result2 = PromptValidationResult(True, [], ["p1"])
        result3 = PromptValidationResult(False, ["p2"], ["p1"])

        assert result1 == result2
        assert result1 != result3
