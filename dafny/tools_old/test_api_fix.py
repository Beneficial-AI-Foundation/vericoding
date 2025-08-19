#!/usr/bin/env python3

import os
import sys

# Add the current directory to the path so we can import vericoder
sys.path.insert(0, '.')

from vericoder import call_api, detect_api_type

def test_api_call():
    """Test the API call with the fixed parameters."""
    try:
        # Test with a simple prompt
        prompt = "Hello, please respond with 'Test successful'"
        
        print("Testing API call...")
        response = call_api(
            prompt,
            model="claude-sonnet-4-20250514",
            timeout=30,
            temperature=0.1,
            max_tokens=100
        )
        
        print(f"API call successful!")
        print(f"Response: {response[:100]}...")
        return True
        
    except Exception as e:
        print(f"API call failed: {e}")
        return False

if __name__ == "__main__":
    test_api_call() 