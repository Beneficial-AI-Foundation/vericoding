#!/usr/bin/env python3
"""
Rewrite vc-description blocks in Verus HumanEval YAMLs to a concise format:
- function_signature: "..."
- requirements: |-  (from pre-conditions)
- ensures: |-      (from post-conditions)

Derives content from the vc-spec block.
"""

from __future__ import annotations

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
    """Return (signature, requires_lines, ensures_lines). spec_block includes header and indented lines.
    """
    # Remove header 'vc-spec: |-' and dedent
    content = [ln[2:] if ln.startswith("  ") else ln for ln in spec_block[1:]]
    # Extract first line starting with 'fn '
    signature = None
    for ln in content:
        if ln.strip().startswith("fn "):
            signature = ln.strip()
            break

    # Find pre/post sections by markers
    requires_lines: list[str] = []
    ensures_lines: list[str] = []
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
            requires_lines.append(ln.strip())
        if in_post:
            ensures_lines.append(ln.strip())

    # Clean trailing empty lines
    while requires_lines and requires_lines[-1] == "":
        requires_lines.pop()
    while ensures_lines and ensures_lines[-1] == "":
        ensures_lines.pop()

    return signature, requires_lines, ensures_lines


def build_description_block(signature: str | None, reqs: list[str], ens: list[str]) -> list[str]:
    block: list[str] = [
        "vc-description: |-",
        "  /--",
    ]
    if signature:
        block.append(f"  function_signature: \"{signature}\"")
    if reqs:
        block.append("  requirements: |-")
        for ln in reqs:
            block.append(f"    {ln}")
    if ens:
        block.append("  ensures: |-")
        for ln in ens:
            block.append(f"    {ln}")
    block.append("  -/")
    return block


def rewrite_file(path: Path) -> bool:
    lines = read_lines(path)
    if lines is None:
        return False

    s_s, s_e, s_block = extract_block(lines, "vc-spec")
    if s_s == -1:
        return False
    signature, reqs, ens = parse_vc_spec(s_block)

    # Build new description block
    desc_block = build_description_block(signature, reqs, ens)

    # Find existing description; if not found, insert after helpers
    d_s, d_e, _ = extract_block(lines, "vc-description")
    if d_s != -1:
        new_lines = lines[:d_s] + desc_block + lines[d_e:]
        write_lines(path, new_lines)
        return True

    h_s, h_e, _ = extract_block(lines, "vc-helpers")
    if h_s != -1:
        new_lines = lines[:h_e] + [""] + desc_block + [""] + lines[h_e:]
        write_lines(path, new_lines)
        return True

    # Fallback: prepend
    new_lines = desc_block + [""] + lines
    write_lines(path, new_lines)
    return True


def main() -> None:
    if not VERUS_DIR.exists():
        print(f"Target dir not found: {VERUS_DIR}")
        return
    changed = 0
    for y in sorted(VERUS_DIR.glob("*.yaml")):
        try:
            if rewrite_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Rewrote vc-description in {changed} Verus YAMLs")


if __name__ == "__main__":
    main()


