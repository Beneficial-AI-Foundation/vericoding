#!/usr/bin/env python3
"""
Add vc-description blocks to Verus Humaneval YAMLs.

Preference per file (NNN-<slug>.yaml or additional__<name>.yaml):
1) Use vc-description from matching Lean file: benchmarks/vericoding_lean/humaneval/HumanEval_N.yaml
2) Otherwise generate a brief description based on the slug/name.

Insertion: place vc-description: |- after vc-helpers and before vc-spec if possible,
otherwise insert at the top.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERUS_DIR = ROOT / "benchmarks" / "verus" / "humaneval"
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


def parse_number_slug(stem: str) -> tuple[int | None, str]:
    # Returns (num, slug)
    if stem.startswith("additional__"):
        return None, stem[len("additional__"):]
    parts = stem.split("-", 1)
    if len(parts) != 2:
        return None, stem
    try:
        num = int(parts[0])
    except Exception:
        return None, stem
    return num, parts[1]


def generate_description_lines(num: int | None, slug: str) -> list[str]:
    title = slug.replace("_", " ") if slug else "task"
    if num is not None:
        doc = f"HumanEval task: {title}. Implement according to the specification."
    else:
        doc = f"Auxiliary Verus task: {title}. Implement according to the specification."
    return ["  /--", f"  docstring: {doc}", "  -/"]


def insert_after_helpers(lines: list[str], desc_block: list[str]) -> list[str]:
    n = len(lines)
    # Find helpers
    i = 0
    while i < n:
        if lines[i].startswith("vc-helpers: |-"):
            j = i + 1
            while j < n and (lines[j].startswith("  ") or lines[j] == ""):
                j += 1
            # Insert a blank line, then description block, then a blank line
            return lines[:j] + [""] + ["vc-description: |-"] + desc_block + [""] + lines[j:]
        i += 1
    # If no helpers, try inserting before vc-spec
    i = 0
    while i < n:
        if lines[i].startswith("vc-spec: |-"):
            return lines[:i] + ["vc-description: |-"] + desc_block + [""] + lines[i:]
        i += 1
    # Fallback: prepend
    return ["vc-description: |-"] + desc_block + [""] + lines


def add_description_to_file(path: Path) -> bool:
    text = read_text(path)
    if text is None:
        return False
    if text.startswith("vc-description: |-") or "\nvc-description: |-" in text:
        return False

    stem = path.stem
    num, slug = parse_number_slug(stem)

    desc_lines: list[str] | None = None
    if num is not None:
        lean_path = LEAN_DIR / f"HumanEval_{num}.yaml"
        lean_text = read_text(lean_path)
        if lean_text:
            desc_lines = extract_vc_description_block(lean_text)

    if desc_lines is None:
        desc_lines = generate_description_lines(num, slug)

    lines = text.splitlines()
    new_lines = insert_after_helpers(lines, desc_lines)
    path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
    return True


def main() -> None:
    if not VERUS_DIR.exists():
        print(f"Target dir not found: {VERUS_DIR}")
        return
    changed = 0
    for y in sorted(VERUS_DIR.glob("*.yaml")):
        try:
            if add_description_to_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Added vc-description to {changed} Verus YAMLs")


if __name__ == "__main__":
    main()


