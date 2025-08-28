"""YAML utilities for specification and code processing."""

import yaml
import re
from pathlib import Path
from typing import Tuple


def load_yaml(yaml_path: Path) -> dict:
    with open(yaml_path, 'r') as f:
        return yaml.safe_load(f) or {}


def yaml_to_code(data: dict, spec: bool = True, vibe: bool = False) -> str:
    """Convert YAML dict to spec, adding section tags based on flags.

    Args:
        data: YAML dictionary
        spec: If True, include vc-spec section
        vibe: If True, include vc-description section
    """
    output: list[str] = []

    # If neither spec nor vibe, return minimal output
    if not spec and not vibe:
        return "// no spec or vibe included"

    # Preamble
    if data.get('vc-preamble'):
        output.append(str(data['vc-preamble']).strip())
        output.append("")

    # Helpers
    output.append("// <vc-helpers>")
    if data.get('vc-helpers'):
        output.append(str(data['vc-helpers']).strip())
    output.append("// </vc-helpers>")
    output.append("")

    # Description (vibe)
    if vibe:
        output.append("// <vc-description>")
        if data.get('vc-description'):
            desc_content = str(data['vc-description']).strip()
            # Use multi-line comment block
            output.append("/*")
            output.append(desc_content)
            output.append("*/")
        output.append("// </vc-description>")
        output.append("")

    # Spec
    if spec:
        output.append("// <vc-spec>")
        if data.get('vc-spec'):
            output.append(str(data['vc-spec']).strip())
        output.append("// </vc-spec>")

    # Code
    output.append("// <vc-code>")
    if data.get('vc-code'):
        output.append(str(data['vc-code']).strip())
    output.append("// </vc-code>")
    output.append("")

    # Postamble
    if data.get('vc-postamble'):
        output.append(str(data['vc-postamble']).strip())

    return "\n".join(output)


def extract_sections(text: str) -> Tuple[str, str, str]:
    """Extract vc-helpers, vc-spec, and vc-code sections from LLM markdown blocks."""

    # Try the expected format first: ```vc-helpers, ```vc-spec, and ```vc-code
    helpers_pattern = r'```vc-helpers\n(.*?)```'
    spec_pattern = r'```vc-spec\n(.*?)```'
    code_pattern = r'```vc-code\n(.*?)```'
    helpers_match = re.search(helpers_pattern, text, re.DOTALL)
    spec_match = re.search(spec_pattern, text, re.DOTALL)
    code_match = re.search(code_pattern, text, re.DOTALL)
    
    # Extract what we find
    helpers = helpers_match.group(1).strip() if helpers_match else ""
    spec = spec_match.group(1).strip() if spec_match else ""
    code = code_match.group(1).strip() if code_match else ""
    
    # For backward compatibility, require at least helpers and code for success
    if helpers_match and code_match:
        return helpers, spec, code
    
    # Fallback: try the format with section names inside dafny/lean/verus blocks
    helpers_pattern_fallback = r'```dafny\nvc-helpers\n(.*?)```'
    spec_pattern_fallback = r'```dafny\nvc-spec\n(.*?)```'
    code_pattern_fallback = r'```dafny\nvc-code\n(.*?)```'
    helpers_match_fallback = re.search(helpers_pattern_fallback, text, re.DOTALL)
    spec_match_fallback = re.search(spec_pattern_fallback, text, re.DOTALL)
    code_match_fallback = re.search(code_pattern_fallback, text, re.DOTALL)
    
    if helpers_match_fallback and code_match_fallback:
        helpers = helpers_match_fallback.group(1).strip()
        spec = spec_match_fallback.group(1).strip() if spec_match_fallback else ""
        code = code_match_fallback.group(1).strip()
        return helpers, spec, code
    
    return "", "", ""


def update_sections(data: dict, helpers: str, code: str, spec: str = "") -> None:
    data['vc-helpers'] = (helpers or "").strip()
    data['vc-code'] = (code or "").strip()
    if spec:  # Only update spec if provided
        data['vc-spec'] = spec.strip()


def save_yaml(output_path: Path, yaml_data: dict) -> None:
    """Save YAML to disk with readable formatting using literal block style."""
    with output_path.open("w") as f:
        for key, value in yaml_data.items():
            if value and value.strip():
                # Non-empty content: use literal block style with content
                f.write(f"{key}: |-\n")
                for line in value.split('\n'):
                    f.write(f"  {line}\n")
            else:
                # Empty content: use literal block style with blank line
                f.write(f"{key}: |-\n\n")
            f.write("\n")
