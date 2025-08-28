#!/usr/bin/env python3
"""
Rename YAMLs like base__method.yaml to collapse duplicated method names when the base already ends
with the same tokens as the method. E.g.:
  034-unique__unique.yaml            -> 034-_unique.yaml
  073-smallest_change__smallest_change.yaml -> 073-_smallest_change.yaml
  001-separate-paren-groups__separate_paren_groups.yaml -> 001-_separate_paren_groups.yaml

Operates in: benchmarks/vericoding_dafny/dafnybench/yaml-humaneval
"""

from __future__ import annotations

import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "benchmarks" / "vericoding_dafny" / "dafnybench" / "yaml-humaneval"


def tokens_with_spans(s: str):
    """Return list of (token, start, end) for alnum tokens in s."""
    return [(m.group(0), m.start(), m.end()) for m in re.finditer(r"[A-Za-z0-9]+", s)]


def split_tokens(s: str):
    return [t for t, _, _ in tokens_with_spans(s)]


def compute_dedup_stem(base_part: str, method: str) -> str | None:
    base_tokens = split_tokens(base_part)
    method_tokens = split_tokens(method)
    if not base_tokens or not method_tokens:
        return None
    # Check if base tokens end with method tokens (case-insensitive)
    if len(base_tokens) < len(method_tokens):
        return None
    tail = base_tokens[-len(method_tokens):]
    if [t.lower() for t in tail] != [t.lower() for t in method_tokens]:
        return None

    # Find span of the first token of the matching tail in base_part
    base_spans = tokens_with_spans(base_part)
    start_idx = base_spans[-len(method_tokens)][1]
    # If there is a non-alnum separator right before, keep it (e.g., '-')
    cut_pos = start_idx
    if cut_pos > 0 and not base_part[cut_pos - 1].isalnum():
        # Keep the separator so we get e.g. "034-" prefix
        prefix = base_part[:cut_pos - 0]  # include separator in prefix
    else:
        prefix = base_part[:cut_pos]

    # Ensure prefix ends with a single non-alnum separator if it already had one
    # We'll just use the existing prefix as-is
    return f"{prefix}_" + method


def main() -> None:
    if not TARGET_DIR.exists():
        print(f"Target directory not found: {TARGET_DIR}")
        return
    yaml_files = sorted(TARGET_DIR.glob("*__*.yaml"))
    renamed = 0
    for path in yaml_files:
        stem = path.stem
        if "__" not in stem:
            continue
        base_part, method = stem.rsplit("__", 1)
        new_stem = compute_dedup_stem(base_part, method)
        if new_stem is None:
            continue
        new_name = new_stem + ".yaml"
        new_path = path.with_name(new_name)
        try:
            if new_path != path:
                if new_path.exists():
                    # Avoid overwriting: skip this rename
                    continue
                os.rename(path, new_path)
                renamed += 1
        except Exception:
            continue
    print(f"Renamed {renamed} files in {TARGET_DIR}")


if __name__ == "__main__":
    main()


