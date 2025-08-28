#!/usr/bin/env python3
"""
Generate informal, human-readable vc-descriptions for Verus additional__* tasks.
Parse the function signature and formal conditions to create natural language descriptions.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERUS_DIR = ROOT / "benchmarks" / "verus" / "humaneval"


def read_lines(path: Path) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except Exception:
        return None


def write_lines(path: Path, lines: list[str]) -> None:
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def extract_block(lines: list[str], key: str) -> tuple[int, int, list[str]]:
    n = len(lines)
    i = 0
    while i < n:
        if lines[i].startswith(f"{key}: |-"):
            j = i + 1
            while j < n and (lines[j].startswith("  ") or lines[j] == ""):
                j += 1
            return i, j, lines[i:j]
        i += 1
    return -1, -1, []


def parse_function_name_and_params(signature: str) -> tuple[str, list[str]]:
    """Extract function name and parameter names from signature."""
    # fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    match = re.match(r'fn\s+(\w+)\s*\((.*?)\)', signature)
    if not match:
        return "function", []
    
    fn_name = match.group(1)
    params_str = match.group(2)
    
    # Extract parameter names
    params = []
    for param in params_str.split(','):
        param = param.strip()
        if ':' in param:
            name = param.split(':')[0].strip()
            params.append(name)
    
    return fn_name, params


def generate_informal_description(fn_name: str, params: list[str], reqs: list[str], ens: list[str]) -> str:
    """Generate an informal description based on function name and conditions."""
    
    # Convert function name to readable form
    readable_name = fn_name.replace('_', ' ')
    
    # Common patterns and their informal descriptions
    if 'binary_search' in fn_name:
        return f"Perform binary search on a sorted array to find the position where an element should be inserted."
    
    if 'rolling_max' in fn_name:
        return f"Compute rolling maximum values over a sliding window in an array."
    
    if 'index_wise_addition' in fn_name:
        return f"Add corresponding elements from two arrays element-wise."
    
    if 'remove_duplicates' in fn_name:
        return f"Remove duplicate elements from an array while preserving order."
    
    if 'largest_prime_factor' in fn_name:
        return f"Find the largest prime factor of a given number."
    
    if 'max_dafny_lsp' in fn_name:
        return f"Find the maximum element in an array."
    
    # Generic fallback based on function name
    if 'sort' in fn_name:
        return f"Sort elements according to specified criteria."
    
    if 'search' in fn_name:
        return f"Search for elements or positions in a data structure."
    
    if 'max' in fn_name or 'min' in fn_name:
        return f"Find the {'maximum' if 'max' in fn_name else 'minimum'} value or element."
    
    if 'add' in fn_name or 'sum' in fn_name:
        return f"Perform addition or summation operations."
    
    if 'count' in fn_name:
        return f"Count occurrences or elements meeting certain criteria."
    
    # Very generic fallback
    return f"Implement {readable_name} functionality."


def parse_vc_spec(spec_block: list[str]) -> tuple[str | None, list[str], list[str]]:
    content = [ln[2:] if ln.startswith("  ") else ln for ln in spec_block[1:]]
    signature = None
    for ln in content:
        if ln.strip().startswith("fn "):
            signature = ln.strip()
            break
    
    requires: list[str] = []
    ensures: list[str] = []
    in_pre = False
    in_post = False
    
    for ln in content:
        s = ln.strip()
        if s == "// pre-conditions-start":
            in_pre = True
            in_post = False
            continue
        if s == "// pre-conditions-end":
            in_pre = False
            continue
        if s == "// post-conditions-start":
            in_post = True
            in_pre = False
            continue
        if s == "// post-conditions-end":
            in_post = False
            continue
        if in_pre and s and not s.startswith("//"):
            requires.append(s)
        if in_post and s and not s.startswith("//"):
            ensures.append(s)
    
    return signature, requires, ensures


def build_description(signature: str | None, reqs: list[str], ens: list[str]) -> list[str]:
    if not signature:
        return ["vc-description: |-", "  /--", "  docstring: Helper function.", "  -/"]
    
    fn_name, params = parse_function_name_and_params(signature)
    docstring = generate_informal_description(fn_name, params, reqs, ens)
    
    return [
        "vc-description: |-",
        "  /--",
        f"  function_signature: \"{signature}\"",
        f"  docstring: {docstring}",
        "  -/"
    ]


def process_file(path: Path) -> bool:
    if not path.stem.startswith("additional__"):
        return False
    
    lines = read_lines(path)
    if lines is None:
        return False
    
    s_s, s_e, s_block = extract_block(lines, "vc-spec")
    if s_s == -1:
        return False
    
    signature, reqs, ens = parse_vc_spec(s_block)
    desc_block = build_description(signature, reqs, ens)
    
    d_s, d_e, _ = extract_block(lines, "vc-description")
    if d_s == -1:
        return False
    
    new_lines = lines[:d_s] + desc_block + lines[d_e:]
    write_lines(path, new_lines)
    return True


def main() -> None:
    if not VERUS_DIR.exists():
        print(f"Target dir not found: {VERUS_DIR}")
        return
    
    changed = 0
    for y in sorted(VERUS_DIR.glob("*.yaml")):
        try:
            if process_file(y):
                changed += 1
        except Exception:
            pass
    
    print(f"Improved descriptions in {changed} additional Verus YAMLs")


if __name__ == "__main__":
    main()
