"""Utility functions for code2verus"""
import re
import subprocess
from pathlib import Path

from code2verus.config import cfg


def check_verus_availability():
    """Check if Verus is available and working"""
    verus_path = cfg.get("verus_path", "verus")
    
    try:
        # Try to run verus with --version flag
        result = subprocess.run(
            [verus_path, "--version"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        
        if result.returncode == 0:
            version_info = result.stdout.strip()
            print(f"Verus found: {version_info}")
            return True
        else:
            print(f"Error: Verus command failed with return code {result.returncode}")
            if result.stderr:
                print(f"Stderr: {result.stderr}")
            return False
            
    except FileNotFoundError:
        print(f"Error: Verus executable not found at '{verus_path}'")
        print("Please ensure Verus is installed and available in your PATH, or update the verus_path in config.yml")
        return False
    except subprocess.TimeoutExpired:
        print("Error: Verus command timed out")
        return False
    except Exception as e:
        print(f"Error checking Verus availability: {e}")
        return False


def extract_rust_code(text: str) -> str:
    """Extract Rust code from markdown code blocks in the agent output"""
    # Pattern to match ```rust ... ``` blocks
    rust_pattern = r"```rust\s*\n(.*?)\n```"
    matches = re.findall(rust_pattern, text, re.DOTALL)

    if matches:
        # Return the first Rust code block found
        return matches[0].strip()

    # If no ```rust blocks found, try ```verus
    verus_pattern = r"```verus\s*\n(.*?)\n```"
    matches = re.findall(verus_pattern, text, re.DOTALL)

    if matches:
        # Return the first Verus code block found
        return matches[0].strip()

    # If no specific blocks found, try generic ```
    generic_pattern = r"```\s*\n(.*?)\n```"
    matches = re.findall(generic_pattern, text, re.DOTALL)

    if matches:
        # Look for the longest code block that looks like Rust/Verus code
        for match in matches:
            code = match.strip()
            # Check if it looks like Rust/Verus code (contains common keywords)
            if any(keyword in code for keyword in ['fn ', 'use ', 'impl ', 'struct ', 'requires', 'ensures', 'proof']):
                return code
        # If no good match, return the first one
        return matches[0].strip()

    # If no code blocks found, return the original text
    return text.strip()
