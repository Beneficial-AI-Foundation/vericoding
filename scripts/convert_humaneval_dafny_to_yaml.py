#!/usr/bin/env python3
"""
Convert Dafny HumanEval .dfy files into vc-*.yaml format used by dafnybench yaml-depsontop.

Rules:
- vc-preamble: everything before the main method signature
- vc-helpers: empty, with markers
- vc-spec: method signature and contracts (requires/ensures), up to but excluding the body '{'
- vc-code: stub body with assume false enclosed in braces
- vc-postamble: empty

Output directory: benchmarks/vericoding_dafny/dafnybench/yaml-humaneval
"""

from __future__ import annotations

import os
import re
from pathlib import Path

# Repository root (vericoding/) is one level up from scripts/
ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "benchmarks" / "dafny" / "humaneval"
TARGET_DIR = ROOT / "benchmarks" / "vericoding_dafny" / "dafnybench" / "yaml-humaneval"


def parse_methods_and_segments(content: str):
    """Parse content into an ordered list of segments: text and methods (excluding lemmas).

    Returns (segments, method_indices) where segments is a list of dicts with keys:
      - type: 'text' or 'method'
      - text: for text segments
      - name, header_lines for method segments
    method_indices is a list of indices in segments that are methods.
    """
    lines = content.splitlines()
    i = 0
    n = len(lines)
    segments: list[dict] = []
    text_buffer: list[str] = []

    def flush_text():
        nonlocal text_buffer
        if text_buffer:
            segments.append({"type": "text", "text": "\n".join(text_buffer)})
            text_buffer = []

    def starts(line: str, prefix: str) -> bool:
        return line.lstrip().startswith(prefix)

    decl_prefixes = (
        "method ",
        "function ",
        "ghost function ",
        "opaque function ",
        "predicate ",
        "datatype ",
        "lemma ",
    )

    while i < n:
        raw = lines[i].lstrip()
        # Skip lemmas entirely
        if starts(raw, "lemma "):
            flush_text()
            # consume lemma header and optional body
            brace_depth = 0
            saw_brace = False
            # Count braces on this line
            if "{" in lines[i]:
                saw_brace = True
                brace_depth += lines[i].count("{")
                brace_depth -= lines[i].count("}")
            i += 1
            if saw_brace:
                while i < n and brace_depth > 0:
                    brace_depth += lines[i].count("{")
                    brace_depth -= lines[i].count("}")
                    i += 1
            else:
                # No body; skip until next declaration
                while i < n and not any(starts(lines[i], p) for p in decl_prefixes):
                    i += 1
            continue

        # Method block
        if starts(raw, "method "):
            flush_text()
            # Extract method name
            m = re.match(r"^\s*method\s+([A-Za-z0-9_]+)", lines[i])
            name = m.group(1) if m else f"method_{len(segments)}"
            # Collect header lines up to before '{'
            header_lines: list[str] = []
            found_brace = False
            j = i
            while j < n:
                line = lines[j]
                if "{" in line:
                    brace_pos = line.find("{")
                    prefix = line[:brace_pos].rstrip()
                    if prefix:
                        header_lines.append(prefix)
                    found_brace = True
                    break
                header_lines.append(line)
                j += 1

            # Consume body to balanced close
            if found_brace:
                brace_depth = lines[j][lines[j].find("{"):].count("{") - lines[j][lines[j].find("{"):].count("}")
                j += 1
                while j < n and brace_depth > 0:
                    brace_depth += lines[j].count("{")
                    brace_depth -= lines[j].count("}")
                    j += 1
            else:
                # No body; treat until next decl
                while j < n and not any(starts(lines[j], p) for p in decl_prefixes):
                    j += 1

            segments.append({
                "type": "method",
                "name": name,
                "header_lines": header_lines,
            })
            i = j
            continue

        # Accumulate as text
        text_buffer.append(lines[i])
        i += 1

    flush_text()

    method_indices = [idx for idx, seg in enumerate(segments) if seg.get("type") == "method"]
    return segments, method_indices


def strip_lemmas_from_text(text: str) -> str:
    """Remove Dafny lemma blocks (headers and bodies) from a text chunk."""
    lines = text.splitlines()
    out: list[str] = []
    skipping = False
    brace_depth = 0
    saw_brace = False

    decl_starts = ("method ", "function ", "ghost function ", "opaque function ", "predicate ", "datatype ")

    for line in lines:
        raw = line.lstrip()
        if not skipping and raw.startswith("lemma "):
            skipping = True
            brace_depth = raw.count("{") - raw.count("}")
            saw_brace = "{" in raw
            # continue to next line without adding this one
            continue

        if skipping:
            # Track braces while skipping
            brace_depth += line.count("{")
            brace_depth -= line.count("}")

            if not saw_brace and any(raw.startswith(s) for s in decl_starts):
                # Lemma without explicit body; stop skipping at next decl
                skipping = False
                out.append(line)
                continue

            if brace_depth <= 0 and saw_brace:
                # Finished skipping lemma body
                skipping = False
            # Do not append skipped lines
            continue

        out.append(line)

    return "\n".join(out)


def to_yaml_block(label: str, lines: list[str]) -> str:
    block = [f"{label}: |-",]
    if lines:
        block.extend([f"  {ln}" for ln in lines])
    return "\n".join(block) + "\n"


def build_method_stub(header_lines: list[str]) -> str:
    stub_lines = []
    stub_lines.extend(header_lines)
    stub_lines.append("{")
    stub_lines.append("  assume{:axiom} false;")
    stub_lines.append("}")
    return "\n".join(stub_lines)


def convert_file(dfy_path: Path, out_dir: Path) -> list[Path]:
    try:
        text = dfy_path.read_text(encoding="utf-8")
    except Exception:
        return []

    # Strip lemmas globally by skipping them during parse
    segments, method_indices = parse_methods_and_segments(text)
    if not method_indices:
        return []

    out_paths: list[Path] = []
    out_dir.mkdir(parents=True, exist_ok=True)

    # Precompute stubs for all methods
    method_stubs = {}
    method_headers = {}
    method_names = []
    mi = 0
    for idx, seg in enumerate(segments):
        if seg["type"] == "method":
            name = seg["name"]
            headers = seg["header_lines"]
            method_names.append(name)
            method_headers[idx] = headers
            method_stubs[idx] = build_method_stub(headers)
            mi += 1

    for main_idx in method_indices:
        # Build preamble: all segments before main_idx
        preamble_lines: list[str] = []
        for idx, seg in enumerate(segments[:main_idx]):
            if seg["type"] == "text":
                preamble_lines.extend(seg["text"].splitlines())
            elif seg["type"] == "method":
                preamble_lines.extend(method_stubs[idx].splitlines())

        # Build postamble: all segments after main_idx
        postamble_lines: list[str] = []
        for idx, seg in enumerate(segments[main_idx+1:], start=main_idx+1):
            if seg["type"] == "text":
                postamble_lines.extend(seg["text"].splitlines())
            elif seg["type"] == "method":
                postamble_lines.extend(method_stubs[idx].splitlines())

        # vc-spec and vc-code for the main method
        vc_spec_lines = list(method_headers[main_idx])
        vc_code_lines = ["{", "  assume false;", "}"]

        yaml_parts: list[str] = []
        yaml_parts.append(to_yaml_block("vc-preamble", preamble_lines))
        yaml_parts.append(to_yaml_block("vc-helpers", []))
        yaml_parts.append(to_yaml_block("vc-spec", vc_spec_lines))
        yaml_parts.append(to_yaml_block("vc-code", vc_code_lines))
        yaml_parts.append(to_yaml_block("vc-postamble", postamble_lines))

        main_name = segments[main_idx]["name"]
        out_path = out_dir / f"{dfy_path.stem}__{main_name}.yaml"
        out_path.write_text("\n".join(yaml_parts), encoding="utf-8")
        out_paths.append(out_path)

    return out_paths


def main() -> None:
    if not SOURCE_DIR.exists():
        print(f"Source directory not found: {SOURCE_DIR}")
        return
    TARGET_DIR.mkdir(parents=True, exist_ok=True)

    dfy_files = sorted(SOURCE_DIR.glob("*.dfy"))
    if not dfy_files:
        print("No .dfy files found to convert.")
        return

    converted = 0
    for f in dfy_files:
        outs = convert_file(f, TARGET_DIR)
        if outs:
            converted += len(outs)

    print(f"Converted {converted} files to {TARGET_DIR}")


if __name__ == "__main__":
    main()


