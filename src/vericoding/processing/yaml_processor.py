"""YAML utilities for specification and code processing."""

import yaml
import re
from pathlib import Path
from typing import Tuple


def load_yaml(yaml_path: Path) -> dict:
    with open(yaml_path, 'r') as f:
        return yaml.safe_load(f) or {}


def yaml_to_code(data: dict) -> str:
    """Convert YAML dict to spec, adding section tags."""
    spec: list[str] = []

    # Preamble
    if data.get('vc-preamble'):
        spec.append(str(data['vc-preamble']).strip())
        spec.append("")

    # Helpers
    spec.append("// <vc-helpers>")
    if data.get('vc-helpers'):
        spec.append(str(data['vc-helpers']).strip())
    spec.append("// </vc-helpers>")
    spec.append("")

    # Spec
    spec.append("// <vc-spec>")
    if data.get('vc-spec'):
        spec.append(str(data['vc-spec']).strip())
    spec.append("// </vc-spec>")
    spec.append("")

    # Code
    spec.append("// <vc-code>")
    if data.get('vc-code'):
        spec.append(str(data['vc-code']).strip())
    spec.append("// </vc-code>")
    spec.append("")

    # Postamble
    if data.get('vc-postamble'):
        spec.append(str(data['vc-postamble']).strip())

    return "\n".join(spec)


def extract_sections(text: str) -> Tuple[str, str]:
    """Extract vc-helpers and vc-code sections from LLM markdown blocks."""

    # Try the expected format first: ```vc-helpers and ```vc-code
    helpers_pattern = r'```vc-helpers\n(.*?)```'
    code_pattern = r'```vc-code\n(.*?)```'
    helpers_match = re.search(helpers_pattern, text, re.DOTALL)
    code_match = re.search(code_pattern, text, re.DOTALL)
    
    if helpers_match and code_match:
        helpers = helpers_match.group(1).strip()
        code = code_match.group(1).strip()
        return helpers, code
    
    # Fallback: try the format with section names inside dafny blocks
    helpers_pattern_fallback = r'```dafny\nvc-helpers\n(.*?)```'
    code_pattern_fallback = r'```dafny\nvc-code\n(.*?)```'
    helpers_match_fallback = re.search(helpers_pattern_fallback, text, re.DOTALL)
    code_match_fallback = re.search(code_pattern_fallback, text, re.DOTALL)
    
    if helpers_match_fallback and code_match_fallback:
        helpers = helpers_match_fallback.group(1).strip()
        code = code_match_fallback.group(1).strip()
        return helpers, code
    
    return "", ""


def update_sections(data: dict, helpers: str, code: str) -> None:
    data['vc-helpers'] = (helpers or "").strip()
    data['vc-code'] = (code or "").strip()


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
