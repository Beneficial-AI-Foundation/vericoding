#!/usr/bin/env python3
"""
Add vc-description blocks to Dafny Humaneval YAMLs.

Preference order per file (NNN-<slug>[__Method].yaml):
1) Use vc-description from matching Lean file: benchmarks/vericoding_lean/humaneval/HumanEval_N.yaml
2) Otherwise generate a brief description based on the slug and method context.

Insertion: place vc-description: |- at the top, before vc-preamble.
"""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DAFNY_DIR = ROOT / "benchmarks" / "vericoding_dafny" / "dafnybench" / "yaml-humaneval"
LEAN_DIR = ROOT / "benchmarks" / "vericoding_lean" / "humaneval"


def read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except Exception:
        return None


def extract_vc_description_block(lean_yaml: str) -> list[str] | None:
    lines = lean_yaml.splitlines()
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        if lines[i].startswith("vc-description: |-"):
            i += 1
            while i < n and (lines[i].startswith("  ") or lines[i] == ""):
                out.append(lines[i])
                i += 1
            return out
        i += 1
    return None


def parse_number_slug(name: str) -> tuple[int | None, str, str | None]:
    # Returns (num, slug, aux_method)
    # stem like: 045-triangle_area__CalculateTriangleArea or 034-_unique
    stem = name
    try:
        num_str, rest = stem.split("-", 1)
        num = int(num_str)
    except Exception:
        return None, stem, None
    aux_method = None
    if "__" in rest:
        slug, aux_method = rest.rsplit("__", 1)
    else:
        slug = rest
    slug = slug.strip()
    if slug.startswith("_"):
        slug = slug[1:]
    return num, slug, aux_method


def generate_description_lines(num: int | None, slug: str, aux_method: str | None) -> list[str]:
    title = slug.replace("_", " ") if slug else "task"
    if aux_method:
        method_title = aux_method
        doc = f"Auxiliary Dafny procedure '{method_title}' used in the HumanEval task '{title}'."
    else:
        doc = f"HumanEval task: {title}. Implement according to the specification."
    lines = ["  /--", f"  docstring: {doc}", "  -/"]
    return lines


def add_description_to_file(path: Path) -> bool:
    text = read_text(path)
    if text is None:
        return False
    if text.startswith("vc-description: |-") or "\nvc-description: |-" in text:
        return False

    # Determine mapping to Lean file
    num, slug, aux = parse_number_slug(path.stem)
    lean_lines: list[str] | None = None
    if num is not None:
        lean_path = LEAN_DIR / f"HumanEval_{num}.yaml"
        lean_text = read_text(lean_path)
        if lean_text:
            lean_lines = extract_vc_description_block(lean_text)

    if lean_lines is None:
        lean_lines = generate_description_lines(num, slug, aux)

    # Insert at top before vc-preamble
    lines = text.splitlines()
    insert_idx = 0
    for i, ln in enumerate(lines):
        if ln.startswith("vc-preamble: |-"):
            insert_idx = i
            break
    new_lines = []
    new_lines.extend(["vc-description: |-", *lean_lines, ""])  # blank line separator
    new_lines.extend(lines)
    path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
    return True


def main() -> None:
    if not DAFNY_DIR.exists():
        print(f"Target dir not found: {DAFNY_DIR}")
        return
    changed = 0
    for y in sorted(DAFNY_DIR.glob("*.yaml")):
        try:
            if add_description_to_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Added vc-description to {changed} files")


if __name__ == "__main__":
    main()


