#!/usr/bin/env python3
"""
Test script for YAML to Lean translation
"""

import os
import sys
from pathlib import Path
from translate_yaml_to_lean import YAMLToLeanTranslator

def test_single_file():
    """Test translation on a single YAML file."""
    
    # Check if API key is provided
    api_key = os.getenv('CLAUDE_API_KEY')
    if not api_key:
        print("Error: Please set CLAUDE_API_KEY environment variable")
        print("Example: export CLAUDE_API_KEY='your-api-key-here'")
        return
    
    # Validate API key
    try:
        from anthropic import Anthropic
        test_client = Anthropic(api_key=api_key)
        response = test_client.messages.create(
            model="claude-3-5-sonnet-20241022",
            max_tokens=10,
            messages=[{"role": "user", "content": "Hello"}]
        )
        print("✓ API key validated successfully")
    except Exception as e:
        print(f"✗ API key validation failed: {e}")
        print("Please check your API key and try again.")
        return
    
    # Find a test YAML file
    yaml_dir = Path("benchmarks/dafny/dafnybench/yaml-depsontop")
    yaml_files = list(yaml_dir.glob("*.yaml"))
    
    if not yaml_files:
        print("No YAML files found")
        return
    
    # Use the first file for testing
    test_file = yaml_files[0]
    print(f"Testing with file: {test_file.name}")
    
    # Create translator
    translator = YAMLToLeanTranslator(api_key)
    
    # Process the test file
    translator.total = 1
    translator.process_file(test_file)
    
    print(f"\nTest completed. Check output in: {translator.output_dir}")

if __name__ == "__main__":
    test_single_file()
