"""YAML utilities for specification and code processing."""

import yaml
import re
from pathlib import Path
from typing import Tuple


def load_yaml(yaml_path: Path) -> dict:
    with open(yaml_path, 'r') as f:
        return yaml.safe_load(f) or {}


def yaml_to_code(data: dict, spec_mode: bool = True, vibe_mode: bool = False) -> str:
    """Convert YAML dict to spec, adding section tags based on flags.

    Args:
        data: YAML dictionary
        spec_mode: If True, include vc-spec section
        vibe_mode: If True, include vc-description section
    """
    output: list[str] = []

    # If neither spec nor vibe, return minimal output
    if not spec_mode and not vibe_mode:
        return "// no spec or vibe included"

    # Preamble
    output.append(str(data['vc-preamble']).strip())
    output.append("")

    # Helpers
    output.append("// <vc-helpers>")
    output.append(str(data['vc-helpers']).strip())
    output.append("// </vc-helpers>")
    output.append("")

    # Description (vibe)
    if vibe_mode:
        output.append("// <vc-description>")
        desc_content = str(data['vc-description']).strip()
        # Use multi-line comment block
        output.append("/*")
        output.append(desc_content)
        output.append("*/")
        output.append("// </vc-description>")
        output.append("")

    # Spec
    output.append("// <vc-spec>")
    if spec_mode:
        output.append(str(data['vc-spec']).strip())
    output.append("// </vc-spec>")
    
    # Code
    output.append("// <vc-code>")
    output.append(str(data['vc-code']).strip())
    output.append("// </vc-code>")
    output.append("")

    # Postamble
    output.append(str(data['vc-postamble']).strip())

    return "\n".join(output)


def extract_sections(text: str) -> Tuple[str, str, str]:
    """Extract vc-helpers, vc-spec, and vc-code sections from LLM markdown blocks.
    
    Be tolerant of:
    - CRLF vs LF newlines
    - Leading whitespace before fences
    - Alternative language fences (e.g., ```dafny or ```dfy for code)
    - Fallback to the first fenced block for code if labeled blocks are missing
    - Missing closing fences: capture until next fence or end-of-text
    """

    def find_block(label: str) -> str:
        # Labeled fence, allowing leading spaces and CRLF, stopping at next fence or end
        pattern = rf'(?ms)^\s*```{label}\s*\r?\n([\s\S]*?)(?:\r?\n\s*```|\Z)'
        m = re.search(pattern, text)
        return m.group(1).strip() if m else ""

    helpers = find_block('vc-helpers')
    spec = find_block('vc-spec')
    code = find_block('vc-code')

    # If code is missing, try alternative labeled fences common to Dafny, Verus, Lean
    if not code:
        alt_labels = ['dafny', 'dfy', 'verus', 'rust', 'rs', 'lean', 'lean4']
        for lbl in alt_labels:
            pattern = rf'(?ms)^\s*```{lbl}\s*\r?\n([\s\S]*?)(?:\r?\n\s*```|\Z)'
            m = re.search(pattern, text)
            if m:
                code = m.group(1).strip()
                break

    # Final fallback: first fenced block of any language or unlabeled
    if not code:
        any_fence = re.search(r'(?ms)^\s*```[^\n]*\r?\n([\s\S]*?)(?:\r?\n\s*```|\Z)', text)
        if any_fence:
            code = any_fence.group(1).strip()

    # Sanitize: strip any stray markdown fence lines that leaked into content
    def strip_fences(s: str) -> str:
        if not s:
            return s
        # Remove any lines that start with ``` (with or without language label)
        s = re.sub(r'(?m)^\s*```.*\n?', '', s)
        return s.strip()

    helpers = strip_fences(helpers)
    spec = strip_fences(spec)
    code = strip_fences(code)

    return helpers, spec, code


def update_sections(data: dict, helpers: str, code: str, spec: str, spec_mode: bool = True) -> None:
    data['vc-helpers'] = (helpers or "").strip()
    data['vc-code'] = (code or "").strip()
    if not spec_mode:  # only update spec if we are not in spec mode
        data['vc-spec'] = (spec or "").strip()



