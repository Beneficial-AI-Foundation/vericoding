#!/usr/bin/env python3
"""
Reposition vc-description in Humaneval YAMLs to be between vc-helpers and vc-spec.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "benchmarks" / "vericoding_dafny" / "dafnybench" / "yaml-humaneval"


def read(path: Path) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except Exception:
        return None


def write(path: Path, lines: list[str]) -> None:
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def extract_block(lines: list[str], key: str) -> tuple[int, int, list[str]]:
    """Return (start_idx, end_idx_exclusive, block_lines_including_header). If not found, (-1, -1, [])."""
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


def run_file(path: Path) -> bool:
    lines = read(path)
    if lines is None:
        return False

    d_s, d_e, d_block = extract_block(lines, "vc-description")
    if d_s == -1:
        return False

    h_s, h_e, h_block = extract_block(lines, "vc-helpers")
    s_s, s_e, s_block = extract_block(lines, "vc-spec")

    if h_s == -1 or s_s == -1:
        return False

    # If description already between helpers and spec, do nothing
    if h_e <= d_s <= s_s:
        return False

    # Remove existing description block
    new_lines = lines[:d_s] + lines[d_e:]

    # Recompute indices after removal
    # Find helpers again in new_lines
    nh_s, nh_e, _ = extract_block(new_lines, "vc-helpers")
    if nh_s == -1:
        return False

    # Insert description after helpers block
    out_lines = new_lines[:nh_e] + [""] + d_block + new_lines[nh_e:]
    write(path, out_lines)
    return True


def main() -> None:
    if not TARGET_DIR.exists():
        print(f"Target dir not found: {TARGET_DIR}")
        return
    changed = 0
    for y in sorted(TARGET_DIR.glob("*.yaml")):
        try:
            if run_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Moved vc-description in {changed} files")


if __name__ == "__main__":
    main()


