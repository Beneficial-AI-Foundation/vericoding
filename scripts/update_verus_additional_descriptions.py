#!/usr/bin/env python3
"""
Rewrite vc-description for Verus additional__* HumanEval YAMLs to include:
- function_signature
- informal requirements (bulleted)
- informal ensures (bulleted)

Derived from vc-spec signature and pre/post blocks, with light pattern-based
naturalization.
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
        if in_pre:
            requires.append(s)
        if in_post:
            ensures.append(s)
    return signature, requires, ensures


def naturalize_line(line: str) -> str:
    # Common patterns
    patterns = [
        (r"forall\|i: int, j: int\| 0 <= i < j < v\.len\(\) ==> v\[i\] <= v\[j\]",
         "array v is nondecreasing (sorted)"),
        (r"0 <= c <= f \+ 1 <= v\.len\(\)",
         "c and f define a valid search window within v (0 ≤ c ≤ f+1 ≤ len(v))"),
        (r"forall\|k: int\| 0 <= k < c ==> v\[k\] <= elem",
         "all elements before c are ≤ elem"),
        (r"forall\|k: int\| f < k < v\.len\(\) ==> v\[k\] > elem",
         "all elements after f are > elem"),
        (r"-1 <= p < v\.len\(\)",
         "p is in [-1, len(v)-1]"),
        (r"forall\|u: int\| 0 <= u <= p ==> v\[u\] <= elem",
         "all indices ≤ p have value ≤ elem"),
        (r"forall\|w: int\| p < w < v\.len\(\) ==> v\[w\] > elem",
         "all indices > p have value > elem"),
    ]
    for pat, rep in patterns:
        if re.fullmatch(pat, line):
            return rep
    # Fallback: lightly clean symbols
    line = line.replace("forall|", "for all ")
    line = line.replace("==>", "implies")
    line = line.replace("&&", "and")
    return line


def build_desc(signature: str | None, reqs: list[str], ens: list[str]) -> list[str]:
    out: list[str] = ["vc-description: |-", "  /--"]
    if signature:
        out.append(f"  function_signature: \"{signature}\"")
    if reqs:
        out.append("  requirements: |-")
        for r in reqs:
            out.append(f"    - {naturalize_line(r)}")
    if ens:
        out.append("  ensures: |-")
        for e in ens:
            out.append(f"    - {naturalize_line(e)}")
    out.append("  -/")
    return out


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
    desc_block = build_desc(signature, reqs, ens)
    d_s, d_e, _ = extract_block(lines, "vc-description")
    if d_s == -1:
        # try insert after helpers
        h_s, h_e, _ = extract_block(lines, "vc-helpers")
        if h_s != -1:
            new_lines = lines[:h_e] + [""] + desc_block + [""] + lines[h_e:]
            write_lines(path, new_lines)
            return True
        new_lines = desc_block + [""] + lines
        write_lines(path, new_lines)
        return True
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
    print(f"Updated descriptions in {changed} additional Verus YAMLs")


if __name__ == "__main__":
    main()


