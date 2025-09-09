"""YAML utilities for specification and code processing."""

import yaml
import re
from pathlib import Path
from typing import Tuple
import sys
sys.path.append(str(Path(__file__).parent.parent.parent))
from convert_from_yaml import spec_to_string, get_template


def load_yaml(yaml_path: Path) -> dict:
    with open(yaml_path, 'r') as f:
        return yaml.safe_load(f) or {}


def yaml_to_code(data: dict, spec_mode: bool = True, vibe_mode: bool = False, language: str = None) -> str:
    """Convert YAML dict to code using appropriate template for the language.

    Args:
        data: YAML dictionary
        spec_mode: If True, include spec-related sections
        vibe_mode: If True, include vc-description section
        language: Language identifier to determine template (lean, dafny, verus)
    """
    # Map language to suffix for get_template function
    suffix_map = {'lean': 'lean', 'dafny': 'dfy', 'verus': 'rs'}
    suffix = suffix_map.get(language, 'dfy')
    
    # Get template and filter based on modes
    template = get_template(suffix)
    filtered_data = data.copy()
    
    # Apply mode filtering
    if not vibe_mode and 'vc-description' in filtered_data:
        del filtered_data['vc-description']
    
    if not spec_mode:
        # Remove spec-related sections
        for key in ['vc-spec', 'vc-definitions', 'vc-theorems']:
            if key in filtered_data:
                del filtered_data[key]
    
    return spec_to_string(filtered_data, template)


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



