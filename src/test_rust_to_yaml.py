#!/usr/bin/env python3
"""
Test script to verify Rust to YAML conversion works correctly.
"""

import yaml
from pathlib import Path
from rust_to_yaml_converter import rust_to_yaml, parse_rust_file


def load_yaml_sections(yaml_path: Path) -> dict:
    """Load YAML file and return the sections."""
    with open(yaml_path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f)


def normalize_whitespace(content: str) -> str:
    """Normalize whitespace for comparison."""
    # Remove trailing whitespace from each line and normalize line endings
    lines = content.splitlines()
    normalized_lines = [line.rstrip() for line in lines]
    # Remove trailing empty lines
    while normalized_lines and not normalized_lines[-1]:
        normalized_lines.pop()
    return '\n'.join(normalized_lines)


def test_conversion_roundtrip(rust_file="053-add.rs"):
    """Test that converting Rust -> YAML -> Rust gives back the original content."""
    
    # Test files
    original_rust_file = Path(f"tests/{rust_file}")
    expected_yaml_file = Path(f"tests/{rust_file}").with_suffix('.yaml')
    
    print("=== Testing Rust to YAML Conversion ===")
    
    # Load original Rust content
    with open(original_rust_file, 'r', encoding='utf-8') as f:
        original_rust = f.read()
    
    print(f"Original Rust file: {original_rust_file}")
    print("Original content:")
    print(repr(original_rust))
    print()
    
    # Convert to YAML
    try:
        converted_yaml = rust_to_yaml(original_rust)
        print("Converted YAML:")
        print(converted_yaml)
        print()
    except Exception as e:
        print(f"ERROR: Failed to convert Rust to YAML: {e}")
        return False
    
    # Load expected YAML for comparison
    expected_yaml_sections = load_yaml_sections(expected_yaml_file)
    print("Expected YAML sections:")
    for key, value in expected_yaml_sections.items():
        print(f"  {key}: {repr(value)}")
    print()
    
    # Parse converted YAML
    try:
        converted_yaml_sections = yaml.safe_load(converted_yaml)
        print("Converted YAML sections:")
        for key, value in converted_yaml_sections.items():
            print(f"  {key}: {repr(value)}")
        print()
    except Exception as e:
        print(f"ERROR: Failed to parse converted YAML: {e}")
        return False
    
    # Compare sections
    print("=== Section Comparison ===")
    success = True
    for key in ['vc-description', 'vc-preamble', 'vc-helpers', 'vc-spec', 'vc-code', 'vc-postamble']:
        expected = expected_yaml_sections.get(key, '')
        converted = converted_yaml_sections.get(key, '')
        
        expected_norm = normalize_whitespace(expected) if expected else ''
        converted_norm = normalize_whitespace(converted) if converted else ''
        
        if expected_norm == converted_norm:
            print(f"✓ {key}: MATCH")
        else:
            print(f"✗ {key}: MISMATCH")
            print(f"  Expected: {repr(expected_norm)}")
            print(f"  Got:      {repr(converted_norm)}")
            success = False
    
    print()
    
    return success


def main():
    """Run the tests."""
    print("Testing Rust to YAML converter...\n")
    
    # Find all YAML test files and derive corresponding .rs files
    yaml_files = list(Path("tests").glob("*.yaml"))
    test_files = []
    
    for yaml_file in yaml_files:
        rust_file = yaml_file.with_suffix('.rs')
        if rust_file.exists():
            test_files.append(rust_file.name)
    
    print(f"Found {len(test_files)} test file pairs: {test_files}\n")
    
    all_passed = True
    
    for test_file in sorted(test_files):
        print(f"Testing {test_file}:")
        if not test_conversion_roundtrip(test_file):
            all_passed = False
        print()
    
    if all_passed:
        print("🎉 All tests passed!")
        return 0
    else:
        print("❌ Some tests failed!")
        return 1


if __name__ == "__main__":
    exit(main())