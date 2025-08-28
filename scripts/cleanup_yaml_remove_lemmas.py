#!/usr/bin/env python3
"""
Remove Dafny lemma blocks from vc-preamble sections in generated YAMLs.

Edits files in-place under benchmarks/vericoding_dafny/dafnybench/yaml-humaneval.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET_DIR = ROOT / "benchmarks" / "dafny" / "humaneval" / "yaml"


def strip_lemmas_from_lines(lines: list[str]) -> list[str]:
    out: list[str] = []
    skipping = False
    brace_depth = 0
    saw_brace = False

    decl_starts = (
        "method ",
        "function ",
        "ghost function ",
        "opaque function ",
        "predicate ",
        "datatype ",
        "lemma ",
    )

    i = 0
    n = len(lines)
    while i < n:
        raw = lines[i].lstrip()
        if not skipping and (raw.startswith("lemma ") or raw.startswith("lemma{:")):
            skipping = True
            # Initialize brace tracking if body starts here
            brace_depth = lines[i].count("{") - lines[i].count("}")
            saw_brace = "{" in lines[i]
            i += 1
            if saw_brace:
                while i < n and brace_depth > 0:
                    brace_depth += lines[i].count("{")
                    brace_depth -= lines[i].count("}")
                    i += 1
            else:
                # No body on header; skip until next declaration-like line or end
                while i < n:
                    nxt = lines[i].lstrip()
                    if any(nxt.startswith(p) for p in decl_starts):
                        break
                    i += 1
            skipping = False
            continue

        out.append(lines[i])
        i += 1

    return out


def strip_block(block_lines: list[str]) -> list[str]:
    # Remove common 2-space indent added by YAML block
    deindented = [ln[2:] if ln.startswith("  ") else ln for ln in block_lines]
    cleaned = strip_lemmas_from_lines(deindented)
    # Re-indent with two spaces for YAML literal block
    return [("  " + ln if ln != "" else "  ") for ln in cleaned]


def process_file(path: Path) -> bool:
    orig = path.read_text(encoding="utf-8").splitlines()
    lines = list(orig)
    n = len(lines)
    changed = False

    def process_section(key: str) -> None:
        nonlocal lines, n, changed
        i = 0
        while i < n:
            if lines[i].startswith(f"{key}: |-"):
                # gather block lines
                j = i + 1
                while j < n and (lines[j].startswith("  ") or lines[j] == ""):
                    j += 1
                block_before = lines[i + 1:j]
                block_after = strip_block(block_before)
                if block_after != block_before:
                    lines[i + 1:j] = block_after
                    delta = len(block_after) - len(block_before)
                    n = len(lines)
                    changed = True
                i = j
            else:
                i += 1

    # Process both preamble and postamble
    process_section("vc-preamble")
    process_section("vc-postamble")

    if changed:
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return changed


def main() -> None:
    if not TARGET_DIR.exists():
        print(f"Target directory not found: {TARGET_DIR}")
        return
    yaml_files = sorted(TARGET_DIR.glob("*.yaml"))
    changed = 0
    for y in yaml_files:
        try:
            if process_file(y):
                changed += 1
        except Exception:
            pass
    print(f"Updated {changed} YAMLs in {TARGET_DIR}")


if __name__ == "__main__":
    main()


