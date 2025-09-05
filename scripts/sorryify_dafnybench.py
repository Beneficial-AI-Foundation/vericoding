#!/usr/bin/env python3
"""
Sorri-fy Lean DafnyBench defs: replace definition bodies with `sorry`.

Heuristics:
- Only touches files under benchmarks/lean/dafnybench/*.lean
- For top-level lines starting with `def` containing `:=`, replace the RHS with `sorry`.
- Remove immediately following indented block lines that continue the same definition body.
- Never touch lines that already contain `sorry` on the same line.

This is conservative but effective for our repository structure.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "benchmarks/lean/dafnybench"

def process_file(p: Path) -> bool:
    text = p.read_text(encoding="utf-8")
    lines = text.splitlines()
    out: list[str] = []
    i = 0
    changed = False
    while i < len(lines):
        line = lines[i]
        # Match top-level def lines (optionally indented 0 spaces) with a := on the same line
        m = re.match(r"^(\s*)def\b.*:=\s*(.*)$", line)
        if m and "sorry" not in line:
            indent = m.group(1)
            # Replace RHS with sorry
            out.append(re.sub(r":=.*$", ":= sorry", line))
            changed = True
            # Drop subsequent indented body lines until next top-level or blank
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                # Stop if next is clearly top-level or empty
                if (not nxt.startswith(" ") and not nxt.startswith("\t")) or re.match(r"^\s*$", nxt):
                    break
                # Also stop on common top-level starters even if not column 0
                if re.match(r"^\s*(def|theorem|lemma|namespace|end|structure|inductive|class|instance|axiom|/-)", nxt):
                    break
                # Otherwise, skip this body line
                j += 1
            i = j
            continue
        else:
            out.append(line)
            i += 1
    if changed:
        p.write_text("\n".join(out) + "\n", encoding="utf-8")
    return changed


def main():
    if not TARGET_DIR.exists():
        print(f"Target dir not found: {TARGET_DIR}")
        return
    lean_files = sorted(TARGET_DIR.glob("*.lean"))
    total = 0
    modified = 0
    for f in lean_files:
        total += 1
        if process_file(f):
            modified += 1
            print(f"sorried: {f.relative_to(ROOT)}")
    print(f"Done. Modified {modified}/{total} files.")


if __name__ == "__main__":
    main()

