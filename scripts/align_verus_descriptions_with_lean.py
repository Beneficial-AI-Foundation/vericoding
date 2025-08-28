#!/usr/bin/env python3
"""
Align Verus HumanEval vc-descriptions to Lean style:
- For numbered tasks (NNN-...), copy the entire vc-description block from the matching Lean file.
- For additional__* tasks, replace the description with a single, informal one-line docstring
  derived from the Verus function name (no formal spec wording).
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERUS_DIR = ROOT / "benchmarks" / "verus" / "humaneval"
LEAN_DIR = ROOT / "benchmarks" / "vericoding_lean" / "humaneval"


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


def parse_task_num_and_slug(stem: str) -> tuple[int | None, str]:
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


def extract_fn_name_from_spec(spec_block: list[str]) -> str | None:
    # spec_block includes header plus indented lines
    for ln in spec_block[1:]:
        s = ln.strip()
        if s.startswith("fn "):
            # fn name(...)
            s2 = s[len("fn "):]
            name = s2.split("(", 1)[0].strip()
            return name
    return None


def align_file(path: Path) -> bool:
    lines = read_lines(path)
    if lines is None:
        return False

    d_s, d_e, _ = extract_block(lines, "vc-description")
    if d_s == -1:
        return False

    num, slug = parse_task_num_and_slug(path.stem)

    if num is not None:
        # Copy from Lean
        lean_path = LEAN_DIR / f"HumanEval_{num}.yaml"
        lean_lines = read_lines(lean_path)
        if not lean_lines:
            return False
        ld_s, ld_e, ld_block = extract_block(lean_lines, "vc-description")
        if ld_s == -1:
            return False
        new_lines = lines[:d_s] + ld_block + lines[d_e:]
        write_lines(path, new_lines)
        return True

    # additional__ task: build simple one-line docstring using fn name
    s_s, s_e, s_block = extract_block(lines, "vc-spec")
    fn_name = extract_fn_name_from_spec(s_block) if s_s != -1 else None
    title = (fn_name or slug or "helper").replace("_", " ")
    doc_block = [
        "vc-description: |-",
        "  /--",
        f"  docstring: Implement {title}.",
        "  -/",
    ]
    new_lines = lines[:d_s] + doc_block + lines[d_e:]
    write_lines(path, new_lines)
    return True


def main() -> None:
    if not VERUS_DIR.exists():
        print(f"Target dir not found: {VERUS_DIR}")
        return
    changed = 0
    for y in sorted(VERUS_DIR.glob("*.yaml")):
        try:
            if align_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Aligned descriptions in {changed} Verus YAMLs")


if __name__ == "__main__":
    main()


