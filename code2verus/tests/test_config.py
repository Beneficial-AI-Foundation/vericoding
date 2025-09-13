"""Test configuration management functionality"""

import pytest
import tempfile
from pathlib import Path
from code2verus.config import load_config, cfg
import yaml


def test_config_loading():
    """Test that config.yml loads correctly"""
    # Test that the global config is loaded
    assert cfg is not None
    assert "verus_path" in cfg
    assert "model" in cfg
    assert "max_translation_iterations" in cfg
    assert "max_retries" in cfg


def test_config_defaults():
    """Test that config has expected default values"""
    assert cfg["verus_path"] == "verus"
    assert cfg["max_translation_iterations"] == 3
    assert cfg["max_retries"] == 16
    assert "forbidden_yaml_fields" in cfg
    assert isinstance(cfg["forbidden_yaml_fields"], list)


def test_system_prompts_exist():
    """Test that required system prompts are configured"""
    assert "system" in cfg
    assert "system_prompts" in cfg
    assert "dafny" in cfg["system_prompts"]
    assert "lean" in cfg["system_prompts"]
    
    # Check that prompts contain critical formatting rules
    dafny_prompt = cfg["system_prompts"]["dafny"]
    assert "use vstd::prelude::*;" in dafny_prompt
    assert "verus! {" in dafny_prompt
    assert "main()" in dafny_prompt
    
    lean_prompt = cfg["system_prompts"]["lean"]
    assert "use vstd::prelude::*;" in lean_prompt
    assert "verus! {" in lean_prompt


def test_yaml_instructions_exist():
    """Test that YAML-specific instructions are configured"""
    assert "yaml_instructions" in cfg
    assert "dafny" in cfg["yaml_instructions"]
    assert "lean" in cfg["yaml_instructions"]
    
    # Check for critical YAML rules
    lean_yaml = cfg["yaml_instructions"]["lean"]
    assert "vc-spec" in lean_yaml
    assert "vc-code" in lean_yaml
    assert "assume(false)" in lean_yaml


def test_config_with_custom_file():
    """Test loading config from a custom file"""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.yml', delete=False) as f:
        test_config = {
            "config": {
                "verus_path": "custom_verus",
                "model": "test_model",
                "max_retries": 5,
                "forbidden_yaml_fields": ["test-field"]
            },
            "system": "test system prompt",
            "system_prompts": {
                "dafny": "test dafny prompt",
                "lean": "test lean prompt"
            }
        }
        yaml.dump(test_config, f)
        f.flush()
        
        # Load the custom config
        custom_cfg = load_config(Path(f.name))
        
        assert custom_cfg["verus_path"] == "custom_verus"
        assert custom_cfg["model"] == "test_model"
        assert custom_cfg["max_retries"] == 5
        assert "test-field" in custom_cfg["forbidden_yaml_fields"]
        
        # Cleanup
        Path(f.name).unlink()


def test_forbidden_fields_configured():
    """Test that forbidden YAML fields are properly configured"""
    forbidden = cfg["forbidden_yaml_fields"]
    expected_forbidden = ["vc-implementation", "vc-signature", "vc-condition", "vc-proof"]
    
    for field in expected_forbidden:
        assert field in forbidden, f"Missing forbidden field: {field}"
