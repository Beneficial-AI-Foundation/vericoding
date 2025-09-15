"""Test configuration management functionality"""

import tempfile
from pathlib import Path
from code2verus.config import load_config, cfg, load_translation_config, merge_configs
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
    with tempfile.NamedTemporaryFile(mode="w", suffix=".yml", delete=False) as f:
        test_config = {
            "config": {
                "verus_path": "custom_verus",
                "model": "test_model",
                "max_retries": 5,
                "forbidden_yaml_fields": ["test-field"],
            },
            "system": "test system prompt",
            "system_prompts": {
                "dafny": "test dafny prompt",
                "lean": "test lean prompt",
            },
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
    expected_forbidden = [
        "vc-implementation",
        "vc-signature",
        "vc-condition",
        "vc-proof",
    ]

    for field in expected_forbidden:
        assert field in forbidden, f"Missing forbidden field: {field}"


def test_merge_configs():
    """Test configuration merging functionality"""
    base_config = {
        "config": {"verus_path": "verus", "model": "base_model"},
        "system": "base system prompt",
    }

    translation_config = {
        "config": {
            "model": "translation_model"  # Should override base
        },
        "system_prompts": {"dafny": "dafny specific prompt"},
    }

    merged = merge_configs(base_config, translation_config)

    # Check that merging works correctly
    assert merged["config"]["verus_path"] == "verus"  # From base
    assert merged["config"]["model"] == "translation_model"  # Overridden
    assert merged["system"] == "base system prompt"  # From base
    assert (
        merged["system_prompts"]["dafny"] == "dafny specific prompt"
    )  # From translation


def test_load_translation_config():
    """Test loading translation-specific configurations"""
    # Test that translation configs can be loaded
    # This will either load from new config structure or fallback to original
    dafny_config = load_translation_config("dafny", "verus")
    assert dafny_config is not None
    assert "config" in dafny_config
    
    lean_config = load_translation_config("lean", "verus")
    assert lean_config is not None
    assert "config" in lean_config
    
    verus_config = load_translation_config("verus", "dafny")
    assert verus_config is not None
    assert "config" in verus_config
    
    # Test the new dafny-to-lean translation
    dafny_lean_config = load_translation_config("dafny", "lean")
    assert dafny_lean_config is not None
    assert "config" in dafny_lean_config


def test_translation_config_contains_system_prompts():
    """Test that translation configs contain language-specific system prompts"""
    dafny_config = load_translation_config("dafny", "verus")

    # Should have either system_prompts section or fallback to system
    has_system_prompts = "system_prompts" in dafny_config
    has_system = "system" in dafny_config
    assert has_system_prompts or has_system, (
        "Translation config should have system prompts"
    )

    if has_system_prompts:
        system_prompts = dafny_config["system_prompts"]
        assert isinstance(system_prompts, dict)


def test_translation_config_inheritance():
    """Test that translation configs properly inherit from base config"""
    base_fields = ["verus_path", "model", "max_translation_iterations", "max_retries"]

    dafny_config = load_translation_config("dafny", "verus")
    config_section = dafny_config.get("config", {})

    for field in base_fields:
        assert field in config_section, (
            f"Translation config missing base field: {field}"
        )


def test_dafny_to_lean_translation_config():
    """Test that dafny-to-lean translation config contains Lean-specific prompts"""
    dafny_lean_config = load_translation_config("dafny", "lean")
    
    # Should have system prompts
    assert "system_prompts" in dafny_lean_config
    assert "dafny" in dafny_lean_config["system_prompts"]
    
    # Check that the prompt is Lean-specific
    prompt = dafny_lean_config["system_prompts"]["dafny"]
    assert "Lean 4" in prompt, "Should mention Lean 4"
    assert "Prop" in prompt, "Should include Prop type for predicates"
    assert "∀" in prompt, "Should include universal quantifier"
    
    # Should have YAML instructions
    assert "yaml_instructions" in dafny_lean_config
    assert "dafny" in dafny_lean_config["yaml_instructions"]
    
    # Should have default prompts
    assert "default_prompts" in dafny_lean_config
    assert "dafny" in dafny_lean_config["default_prompts"]
