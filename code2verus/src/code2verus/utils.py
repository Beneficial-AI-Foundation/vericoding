"""Utility functions for code2verus"""

import re
import subprocess
import yaml
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
        print(
            "Please ensure Verus is installed and available in your PATH, or update the verus_path in config.yml"
        )
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
            if any(
                keyword in code
                for keyword in [
                    "fn ",
                    "use ",
                    "impl ",
                    "struct ",
                    "requires",
                    "ensures",
                    "proof",
                ]
            ):
                return code
        # If no good match, return the first one
        return matches[0].strip()

    # If no code blocks found, return the original text
    return text.strip()


def concatenate_yaml_fields(yaml_content: str) -> str:
    """Parse YAML content and concatenate all field values to create a single Verus file"""
    try:
        # Parse the YAML content
        data = yaml.safe_load(yaml_content)

        if not isinstance(data, dict):
            # If it's not a dict, return the original content
            return yaml_content

        # Define the expected order of fields for Verus code
        field_order = [
            "vc-description",
            "vc-preamble",
            "vc-helpers",
            "vc-spec",
            "vc-code",
            "vc-postamble",
        ]

        parts = []

        # Process description as a comment
        if "vc-description" in data and data["vc-description"]:
            description = str(data["vc-description"]).strip()
            if description:
                # Add as a block comment
                parts.append(f"/* {description} */")
                parts.append("")  # Empty line after description

        # Process other fields in order
        for field in field_order[1:]:  # Skip vc-description as we handled it above
            if field in data and data[field]:
                content = str(data[field]).strip()
                if content:
                    parts.append(content)

        return "\n".join(parts)

    except yaml.YAMLError as e:
        # If YAML parsing fails, return the original content
        return yaml_content
    except Exception as e:
        # For any other error, return the original content
        return yaml_content
