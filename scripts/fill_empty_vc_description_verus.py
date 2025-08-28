#!/usr/bin/env python3
"""
Fill empty vc-description blocks in Verus HumanEval YAMLs.

If a file has a vc-description: |- header with no content lines, insert a concise description.
Prefer copying from Lean HumanEval when a numeric ID exists; otherwise generate from slug.
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


def extract_desc(lines: list[str]) -> tuple[int, int, list[str]]:
    n = len(lines)
    i = 0
    while i < n:
        if lines[i].startswith("vc-description: |-"):
            j = i + 1
            block: list[str] = []
            while j < n and (lines[j].startswith("  ") or lines[j] == ""):
                block.append(lines[j])
                j += 1
            return i, j, block
        i += 1
    return -1, -1, []


def get_lean_desc_block(num: int) -> list[str] | None:
    p = LEAN_DIR / f"HumanEval_{num}.yaml"
    t = read_text(p)
    if not t:
        return None
    lines = t.splitlines()
    _, _, block = extract_desc(lines)
    return block or None


def parse_num_and_slug(stem: str) -> tuple[int | None, str]:
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


def make_fallback_desc(num: int | None, slug: str) -> list[str]:
    title = slug.replace("_", " ") if slug else "task"
    if num is not None:
        doc = f"HumanEval task: {title}. Implement according to the specification."
    else:
        doc = f"Auxiliary Verus task: {title}. Implement according to the specification."
    return ["  /--", f"  docstring: {doc}", "  -/"]


def fill_file(path: Path) -> bool:
    text = read_text(path)
    if text is None:
        return False
    lines = text.splitlines()
    d_s, d_e, block = extract_desc(lines)
    if d_s == -1:
        return False
    # Check if empty (no non-empty content lines)
    has_content = any(ln.strip() != "" for ln in block)
    if has_content:
        return False

    num, slug = parse_num_and_slug(path.stem)
    new_block = None
    if num is not None:
        new_block = get_lean_desc_block(num)
    if new_block is None:
        new_block = make_fallback_desc(num, slug)

    lines[d_s+1:d_e] = new_block + [""]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return True


def main() -> None:
    if not VERUS_DIR.exists():
        print(f"Target dir not found: {VERUS_DIR}")
        return
    changed = 0
    for y in sorted(VERUS_DIR.glob("*.yaml")):
        try:
            if fill_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Filled empty vc-description in {changed} Verus YAMLs")


if __name__ == "__main__":
    main()


