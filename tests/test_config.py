"""Test configuration validation and language configurations."""

import pytest
from vericoding.core.config import ProcessingConfig


class TestConfiguration:
    """Test configuration loading and validation."""

    def test_available_languages_exist(self):
        """Test that get_available_languages returns a non-empty dict."""
        languages = ProcessingConfig.get_available_languages()
        assert isinstance(languages, dict)
        assert len(languages) > 0

    def test_language_configurations_valid(self):
        """Test that all configured languages have valid configurations."""
        languages = ProcessingConfig.get_available_languages()
        
        for lang_name, lang_config in languages.items():
            # Test required attributes exist
            assert hasattr(lang_config, 'name'), f'{lang_name} missing name'
            assert hasattr(lang_config, 'file_extension'), f'{lang_name} missing file_extension'
            assert hasattr(lang_config, 'tool_path_env'), f'{lang_name} missing tool_path_env'
            assert hasattr(lang_config, 'prompts_file'), f'{lang_name} missing prompts_file'
            
            # Test that attributes have reasonable values
            assert lang_config.name, f'{lang_name} has empty name'
            assert lang_config.file_extension, f'{lang_name} has empty file_extension'
            assert lang_config.tool_path_env, f'{lang_name} has empty tool_path_env'
            assert lang_config.prompts_file, f'{lang_name} has empty prompts_file'

    def test_language_configuration_types(self):
        """Test that language configuration attributes are of correct types."""
        languages = ProcessingConfig.get_available_languages()
        
        for lang_name, lang_config in languages.items():
            assert isinstance(lang_config.name, str), f'{lang_name}.name should be string'
            assert isinstance(lang_config.file_extension, str), f'{lang_name}.file_extension should be string'
            assert isinstance(lang_config.tool_path_env, str), f'{lang_name}.tool_path_env should be string'
            assert isinstance(lang_config.prompts_file, str), f'{lang_name}.prompts_file should be string'
