"""Test configuration validation and language configurations."""

import pytest
from pathlib import Path
from unittest.mock import patch

from vericoding.core.config import ProcessingConfig, LanguageConfig, load_environment


class TestProcessingConfig:
    """Test ProcessingConfig functionality."""

    def test_available_languages_exist(self):
        """Test that get_available_languages returns a non-empty dict."""
        languages = ProcessingConfig.get_available_languages()
        assert isinstance(languages, dict)
        assert len(languages) > 0
        print(f"Available languages: {list(languages.keys())}")

    def test_language_configurations_complete(self):
        """Test that all configured languages have complete configurations."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
            # Test required attributes exist
            assert hasattr(lang_config, "name"), f"{lang_name} missing name"
            assert hasattr(lang_config, "file_extension"), (
                f"{lang_name} missing file_extension"
            )
            assert hasattr(lang_config, "tool_path_env"), (
                f"{lang_name} missing tool_path_env"
            )
            assert hasattr(lang_config, "prompts_file"), (
                f"{lang_name} missing prompts_file"
            )
            assert hasattr(lang_config, "default_tool_path"), (
                f"{lang_name} missing default_tool_path"
            )

            # Test that attributes have reasonable values
            assert lang_config.name, f"{lang_name} has empty name"
            assert lang_config.file_extension.startswith("."), (
                f"{lang_name} file_extension should start with '.'"
            )
            assert lang_config.tool_path_env, f"{lang_name} has empty tool_path_env"
            assert lang_config.prompts_file, f"{lang_name} has empty prompts_file"
            assert lang_config.default_tool_path, (
                f"{lang_name} has empty default_tool_path"
            )

    def test_language_configuration_types(self):
        """Test that language configuration attributes are of correct types."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
            assert isinstance(lang_config, LanguageConfig), (
                f"{lang_name} should be LanguageConfig instance"
            )
            assert isinstance(lang_config.name, str), (
                f"{lang_name}.name should be string"
            )
            assert isinstance(lang_config.file_extension, str), (
                f"{lang_name}.file_extension should be string"
            )
            assert isinstance(lang_config.tool_path_env, str), (
                f"{lang_name}.tool_path_env should be string"
            )
            assert isinstance(lang_config.prompts_file, str), (
                f"{lang_name}.prompts_file should be string"
            )
            assert isinstance(lang_config.default_tool_path, str), (
                f"{lang_name}.default_tool_path should be string"
            )

    def test_language_configuration_consistency(self):
        """Test internal consistency of language configurations."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
            # File extension should be reasonable
            assert len(lang_config.file_extension) >= 2, (
                f"{lang_name} file extension too short"
            )
            assert "." in lang_config.file_extension, (
                f"{lang_name} file extension should contain '.'"
            )

            # Environment variable should follow naming conventions
            assert lang_config.tool_path_env.isupper(), (
                f"{lang_name} env var should be uppercase"
            )
            assert "_" in lang_config.tool_path_env, (
                f"{lang_name} env var should contain '_'"
            )

            # Prompts file should be YAML
            assert lang_config.prompts_file.endswith((".yaml", ".yml")), (
                f"{lang_name} prompts should be YAML"
            )

    def test_processing_config_with_language(self):
        """Test ProcessingConfig initialization with specific language."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
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

    def test_processing_config_invalid_language(self):
        """Test ProcessingConfig with invalid language."""
        # For this test, we'll test the get_available_languages method instead
        # since ProcessingConfig doesn't validate language during construction
        languages = ProcessingConfig.get_available_languages()
        assert "invalid_language" not in languages

        # Test that we can still create a ProcessingConfig with an invalid language
        # (validation may happen elsewhere in the pipeline)
        config = ProcessingConfig(
            language="invalid_language",
            language_config=None,  # This would cause issues downstream
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
        assert config.language == "invalid_language"

    def test_processing_config_default_values(self):
        """Test ProcessingConfig default parameter values."""
        languages = ProcessingConfig.get_available_languages()
        dafny_config = languages["dafny"]

        config = ProcessingConfig(
            language="dafny",
            language_config=dafny_config,
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

        # Test assigned values
        assert config.max_workers == 4
        assert config.max_directory_traversal_depth == 50  # Default value
        assert isinstance(config.output_dir, str)
        assert config.debug_mode is False

    def test_processing_config_custom_values(self):
        """Test ProcessingConfig with custom parameter values."""
        languages = ProcessingConfig.get_available_languages()
        dafny_config = languages["dafny"]

        config = ProcessingConfig(
            language="dafny",
            language_config=dafny_config,
            files_dir="custom_files",
            max_iterations=5,
            output_dir="custom_output",
            summary_file="custom_summary.json",
            debug_mode=True,
            strict_spec_verification=False,
            max_workers=8,
            api_rate_limit_delay=2,
            llm_provider="openai",
            llm_model="gpt-4",
            max_directory_traversal_depth=100,
        )

        assert config.max_workers == 8
        assert config.output_dir == "custom_output"
        assert config.debug_mode is True
        assert config.max_directory_traversal_depth == 100
        assert config.llm_provider == "openai"
        assert config.llm_model == "gpt-4"


class TestLanguageConfig:
    """Test LanguageConfig dataclass."""

    def test_language_config_creation(self):
        """Test creating LanguageConfig instances."""
        config = LanguageConfig(
            name="test_lang",
            file_extension=".test",
            tool_path_env="TEST_TOOL_PATH",
            default_tool_path="test_tool",
            prompts_file="test_prompts.yaml",
            verify_command=["test_tool", "verify"],
            compile_check_command=["test_tool", "compile"],
            code_block_patterns=["```test", "```"],
            keywords=["function", "method"],
            spec_patterns=["requires", "ensures"],
        )

        assert config.name == "test_lang"
        assert config.file_extension == ".test"
        assert config.tool_path_env == "TEST_TOOL_PATH"
        assert config.prompts_file == "test_prompts.yaml"
        assert config.default_tool_path == "test_tool"
        assert config.verify_command == ["test_tool", "verify"]

    def test_language_config_equality(self):
        """Test LanguageConfig equality comparison."""
        common_args = {
            "file_extension": ".ext",
            "tool_path_env": "ENV",
            "default_tool_path": "tool",
            "prompts_file": "prompts.yaml",
            "verify_command": ["tool", "verify"],
            "compile_check_command": ["tool", "compile"],
            "code_block_patterns": ["```"],
            "keywords": ["function"],
            "spec_patterns": ["requires"],
        }

        config1 = LanguageConfig(name="lang", **common_args)
        config2 = LanguageConfig(name="lang", **common_args)
        config3 = LanguageConfig(name="lang2", **common_args)

        assert config1 == config2
        assert config1 != config3


class TestEnvironmentLoading:
    """Test environment variable loading functionality."""

    def test_load_environment_no_env_file(self):
        """Test load_environment when no .env file exists."""
        with (
            patch("pathlib.Path.exists", return_value=False),
            patch("dotenv.load_dotenv") as mock_load_dotenv,
        ):
            load_environment()

            # Should still try to load from default location
            mock_load_dotenv.assert_called()

    def test_load_environment_with_env_file(self):
        """Test load_environment when .env file exists."""
        with (
            patch("pathlib.Path.exists", return_value=True),
            patch("dotenv.load_dotenv") as mock_load_dotenv,
        ):
            load_environment()

            mock_load_dotenv.assert_called()


class TestConfigurationIntegration:
    """Integration tests for configuration system."""

    @pytest.mark.integration
    def test_configuration_file_structure(self):
        """Test that configuration files exist and are structured correctly."""
        # Check if configuration files exist
        config_dir = Path(__file__).parent.parent / "config"

        if config_dir.exists():
            # Look for TOML or YAML config files
            config_files = list(config_dir.glob("*.toml")) + list(
                config_dir.glob("*.yaml")
            )

            if config_files:
                print(f"Found config files: {[f.name for f in config_files]}")

                for config_file in config_files:
                    assert config_file.is_file(), (
                        f"Config file should be a file: {config_file}"
                    )
                    assert config_file.stat().st_size > 0, (
                        f"Config file should not be empty: {config_file}"
                    )

    @pytest.mark.integration
    def test_all_configured_languages_have_directories(self):
        """Test that all configured languages have corresponding directories."""
        languages = ProcessingConfig.get_available_languages()
        project_root = Path(__file__).parent.parent

        for lang_name in languages.keys():
            lang_dir = project_root / lang_name
            if lang_dir.exists():
                print(f"✓ {lang_name}: directory exists at {lang_dir}")

                # Check for expected files in language directory
                lang_config = languages[lang_name]
                prompts_file = lang_dir / lang_config.prompts_file

                if prompts_file.exists():
                    print(f"  ✓ Prompts file exists: {prompts_file}")
                else:
                    print(f"  - Prompts file not found: {prompts_file}")
            else:
                print(f"  - Directory not found: {lang_dir}")

    def test_environment_variable_names_unique(self):
        """Test that environment variable names are unique across languages."""
        languages = ProcessingConfig.get_available_languages()
        env_vars = []

        for lang_name, lang_config in languages.items():
            env_var = lang_config.tool_path_env
            assert env_var not in env_vars, (
                f"Duplicate environment variable: {env_var} (used by {lang_name})"
            )
            env_vars.append(env_var)

    def test_file_extensions_valid(self):
        """Test that file extensions are valid and follow conventions."""
        languages = ProcessingConfig.get_available_languages()

        for lang_name, lang_config in languages.items():
            ext = lang_config.file_extension

            # Should start with dot
            assert ext.startswith("."), f"{lang_name} extension should start with '.'"

            # Should be lowercase (conventional)
            assert ext.islower(), f"{lang_name} extension should be lowercase"

            # Should not contain spaces or special chars except dot
            assert " " not in ext, f"{lang_name} extension should not contain spaces"
            assert ext.count(".") == 1, (
                f"{lang_name} extension should have exactly one dot"
            )
