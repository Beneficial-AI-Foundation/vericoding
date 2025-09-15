"""Utility functions for code2verus"""

import re
import subprocess
import yaml
import logfire

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


def yaml_to_lean(lean_yaml: str) -> str:
    """Convert YAML format to Lean code by extracting and concatenating sections.
    
    This is specifically for Lean and follows the VeriCoding verina format which
    does NOT include vc-description as a comment.
    """
    try:
        # Parse the YAML content
        parsed_yaml = yaml.safe_load(lean_yaml)

        # Ensure the parsed YAML is a dictionary before processing
        if not isinstance(parsed_yaml, dict):
            logfire.error(
                f"YAML did not parse to a dictionary, got {type(parsed_yaml)}: {parsed_yaml}"
            )
            raise ValueError(
                f"Expected YAML to be a dictionary, got {type(parsed_yaml)}"
            )

        # Extract and concatenate YAML sections (skip vc-description for Lean)
        parts = []

        # Add sections in the expected order for Lean YAML structure with proper formatting
        # For Lean, we need to wrap sections in comment blocks to match the expected format
        
        # Handle preamble
        if "vc-preamble" in parsed_yaml and parsed_yaml["vc-preamble"]:
            content = str(parsed_yaml["vc-preamble"]).strip()
            if content:
                parts.append("-- <vc-preamble>")
                parts.append(content)
                parts.append("-- </vc-preamble>")
                parts.append("")
        
        # Handle helpers
        if "vc-helpers" in parsed_yaml and parsed_yaml["vc-helpers"]:
            content = str(parsed_yaml["vc-helpers"]).strip()
            parts.append("-- <vc-helpers>")
            if content:
                parts.append(content)
            parts.append("-- </vc-helpers>")
            parts.append("")
        else:
            parts.append("-- <vc-helpers>")
            parts.append("-- </vc-helpers>")
            parts.append("")
        
        # Handle definitions (signature + implementation)
        parts.append("-- <vc-definitions>")
        if "vc-signature" in parsed_yaml and parsed_yaml["vc-signature"]:
            signature = str(parsed_yaml["vc-signature"]).strip()
            if signature:
                parts.append(signature)
        
        if "vc-implementation" in parsed_yaml and parsed_yaml["vc-implementation"]:
            implementation = str(parsed_yaml["vc-implementation"]).strip()
            if implementation:
                parts.append(implementation)
        parts.append("-- </vc-definitions>")
        parts.append("")
        
        # Handle theorems (condition + proof)
        parts.append("-- <vc-theorems>")
        if "vc-condition" in parsed_yaml and parsed_yaml["vc-condition"]:
            condition = str(parsed_yaml["vc-condition"]).strip()
            if condition:
                parts.append(condition)
        
        if "vc-proof" in parsed_yaml and parsed_yaml["vc-proof"]:
            proof = str(parsed_yaml["vc-proof"]).strip()
            if proof:
                parts.append(proof)
        parts.append("-- </vc-theorems>")
        
        # Handle postamble
        if "vc-postamble" in parsed_yaml and parsed_yaml["vc-postamble"]:
            content = str(parsed_yaml["vc-postamble"]).strip()
            if content:
                parts.append("")
                parts.append(content)

        # Check if no valid content was found
        if not parts:
            logfire.warning(
                "No valid Lean content found in YAML - all sections are empty"
            )
            raise ValueError(
                "No valid Lean content found: all YAML sections (vc-preamble, vc-helpers, vc-signature, vc-implementation, vc-condition, vc-proof, vc-postamble) are empty or missing"
            )

        return "\n".join(parts)

    except yaml.YAMLError as e:
        logfire.error(f"YAML parsing failed: {e}")
        logfire.info(
            f"Failed YAML content (first 500 chars): {lean_yaml[: min(500, len(lean_yaml))]}..."
        )
        # Fall back to using the content as-is
        logfire.info("Using YAML content as-is despite parsing error")
        return lean_yaml

    except Exception as e:
        logfire.error(f"Unexpected error during YAML processing: {e}")
        logfire.info(f"Failed to parse YAML, using as-is: {e}")
        return lean_yaml


def yaml_to_verus(verus_yaml: str, format_description_as_comment: bool = False) -> str:
    """Convert YAML format to Verus code by extracting and concatenating sections.

    Extracts valid sections from YAML (vc-description, vc-preamble, vc-helpers,
    vc-spec, vc-code, vc-postamble) and concatenates them with newlines.

    Args:
        verus_yaml: YAML string containing Verus code sections
        format_description_as_comment: If True, format vc-description as a block comment

    Returns:
        Concatenated Verus code from all non-empty sections

    Raises:
        ValueError: If YAML doesn't parse to a dictionary, contains forbidden fields,
                   or all sections are empty/missing

    Note:
        If YAML parsing fails, the original string is returned as-is.
    """
    try:
        # Parse the YAML content
        parsed_yaml = yaml.safe_load(verus_yaml)

        # Ensure the parsed YAML is a dictionary before processing
        if not isinstance(parsed_yaml, dict):
            logfire.error(
                f"YAML did not parse to a dictionary, got {type(parsed_yaml)}: {parsed_yaml}"
            )
            raise ValueError(
                f"Expected YAML to be a dictionary, got {type(parsed_yaml)}"
            )

        # Check for forbidden fields and raise an error if found
        forbidden_fields = cfg.get(
            "forbidden_yaml_fields",
            [
                "vc-implementation",
                "vc-signature",
                "vc-condition",
                "vc-proof",
            ],
        )
        found_forbidden = [field for field in forbidden_fields if field in parsed_yaml]

        if found_forbidden:
            error_msg = (
                f"Error: Found forbidden fields in YAML: {', '.join(found_forbidden)}"
            )
            logfire.error(error_msg)
            raise ValueError(error_msg)

        # Extract and concatenate YAML sections
        parts = []

        # Handle vc-description with optional comment formatting
        if "vc-description" in parsed_yaml and parsed_yaml["vc-description"]:
            description = str(parsed_yaml["vc-description"]).strip()
            if description:
                if format_description_as_comment:
                    parts.append(f"/* {description} */")
                    parts.append("")  # Empty line after description
                else:
                    parts.append(description)

        # Add other sections in the expected order
        section_fields = [
            "vc-preamble",
            "vc-helpers",
            "vc-spec",
            "vc-code",
            "vc-postamble",
        ]
        for field in section_fields:
            if field in parsed_yaml and parsed_yaml[field]:
                content = str(parsed_yaml[field]).strip()
                if content:
                    parts.append(content)

        # Check if no valid content was found
        if not parts:
            logfire.warning(
                "No valid Verus content found in YAML - all sections are empty"
            )
            raise ValueError(
                "No valid Verus content found: all YAML sections (vc-description, vc-preamble, vc-helpers, vc-spec, vc-code, vc-postamble) are empty or missing"
            )

        return "\n".join(parts)

    except yaml.YAMLError as e:
        logfire.error(f"YAML parsing failed: {e}")
        logfire.info(
            f"Failed YAML content (first 500 chars): {verus_yaml[: min(500, len(verus_yaml))]}..."
        )

        # Try to provide more specific error information for common issues
        error_msg = str(e)
        if "mapping values are not allowed here" in error_msg:
            logfire.error(
                "YAML Error: Likely indentation or syntax issue. Common causes:"
            )
            logfire.error("- Missing colons after field names")
            logfire.error("- Incorrect indentation")
            logfire.error("- Special characters not properly quoted")

        # Fall back to using the content as-is
        logfire.info("Using YAML content as-is despite parsing error")
        return verus_yaml

    except Exception as e:
        logfire.error(f"Unexpected error during YAML processing: {e}")
        logfire.info(f"Failed to parse YAML, using as-is: {e}")
        return verus_yaml


def yaml_to_dafny(dafny_yaml: str) -> str:
    """Convert YAML format to Dafny code by extracting and concatenating sections.
    
    This follows the Dafny format which uses comment blocks to mark sections.
    """
    try:
        # Parse the YAML content
        parsed_yaml = yaml.safe_load(dafny_yaml)

        # Ensure the parsed YAML is a dictionary before processing
        if not isinstance(parsed_yaml, dict):
            logfire.error(
                f"YAML did not parse to a dictionary, got {type(parsed_yaml)}: {parsed_yaml}"
            )
            raise ValueError(
                f"Expected YAML to be a dictionary, got {type(parsed_yaml)}"
            )

        # Extract and concatenate YAML sections
        parts = []

        # Handle preamble
        if "vc-preamble" in parsed_yaml and parsed_yaml["vc-preamble"]:
            content = str(parsed_yaml["vc-preamble"]).strip()
            if content:
                parts.append("// <vc-preamble>")
                parts.append(content)
                parts.append("// </vc-preamble>")
                parts.append("")
        
        # Handle helpers
        if "vc-helpers" in parsed_yaml and parsed_yaml["vc-helpers"]:
            content = str(parsed_yaml["vc-helpers"]).strip()
            parts.append("// <vc-helpers>")
            if content:
                parts.append(content)
            parts.append("// </vc-helpers>")
            parts.append("")
        else:
            parts.append("// <vc-helpers>")
            parts.append("// </vc-helpers>")
            parts.append("")
        
        # Handle spec
        if "vc-spec" in parsed_yaml and parsed_yaml["vc-spec"]:
            content = str(parsed_yaml["vc-spec"]).strip()
            if content:
                parts.append("// <vc-spec>")
                parts.append(content)
                parts.append("// </vc-spec>")
                parts.append("")
        
        # Handle code
        if "vc-code" in parsed_yaml and parsed_yaml["vc-code"]:
            content = str(parsed_yaml["vc-code"]).strip()
            if content:
                parts.append("// <vc-code>")
                parts.append(content)
                parts.append("// </vc-code>")
        
        # Handle postamble
        if "vc-postamble" in parsed_yaml and parsed_yaml["vc-postamble"]:
            content = str(parsed_yaml["vc-postamble"]).strip()
            if content:
                parts.append(content)

        # Check if no valid content was found
        if not parts:
            logfire.warning(
                "No valid Dafny content found in YAML - all sections are empty"
            )
            raise ValueError(
                "No valid Dafny content found: all YAML sections are empty or missing"
            )

        return "\n".join(parts)

    except yaml.YAMLError as e:
        logfire.error(f"YAML parsing failed: {e}")
        # Fall back to using the content as-is
        return dafny_yaml

    except Exception as e:
        logfire.error(f"Unexpected error during YAML processing: {e}")
        return dafny_yaml


def concatenate_yaml_fields(yaml_content: str) -> str:
    """Parse YAML content and concatenate all field values to create a single Verus file

    This function is deprecated. Use yaml_to_verus(yaml_content, format_description_as_comment=True) instead.
    """
    return yaml_to_verus(yaml_content, format_description_as_comment=True)
