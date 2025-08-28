#!/usr/bin/env python3
"""
Normalize spacing in Humaneval YAMLs: collapse multiple consecutive empty lines into a single empty line.
This preserves YAML literal block content (which uses two-space-indented lines), since only truly empty
lines are collapsed.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "benchmarks" / "vericoding_dafny" / "dafnybench" / "yaml-humaneval"


def normalize(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    out: list[str] = []
    prev_empty = False
    for ln in lines:
        if ln == "":
            if prev_empty:
                continue
            prev_empty = True
            out.append(ln)
        else:
            prev_empty = False
            out.append(ln)
    new_text = "\n".join(out) + "\n"
    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
        return True
    return False


def main() -> None:
    if not TARGET_DIR.exists():
        print(f"Target dir not found: {TARGET_DIR}")
        return
    changed = 0
    for y in sorted(TARGET_DIR.glob("*.yaml")):
        try:
            if normalize(y):
                changed += 1
        except Exception:
            pass
    print(f"Normalized spacing in {changed} files")


if __name__ == "__main__":
    main()


