#!/usr/bin/env python3
"""
Generate Lean YAML stubs for DafnyBench-style problems.

This script reads Lean specs from `lean/DafnyBenchSpecs` and emits YAML files
under `benchmarks/lean/dafnybench/yaml-depsontop` whose filenames match the
existing Dafny YAML names in `benchmarks/dafny/dafnybench/yaml-depsontop` when
possible. When no good match is found, the file is skipped (and reported).

The emitted YAML follows `benchmarks/lean/template.yaml` structure:
  - vc-description: extracted from the first top-of-file doc comment, if any
  - vc-preamble: left empty
  - vc-helpers: empty block with markers
  - vc-signature: stub using the first `def` name, if any
  - vc-implementation: empty block with markers
  - vc-condition: stub using the first `theorem` name, if any
  - vc-proof: empty block with markers
  - vc-postamble: includes a comment pointing to the source Lean file

Run:
  uv run scripts/gen_lean_dafnybench_yaml.py --write
"""
from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple


ROOT = Path(__file__).resolve().parents[1]
LEAN_SRC = ROOT / "lean" / "DafnyBenchSpecs"
DAFNY_YAML = ROOT / "benchmarks" / "dafny" / "dafnybench" / "yaml-depsontop"
LEAN_YAML_OUT = ROOT / "benchmarks" / "lean" / "dafnybench" / "yaml-depsontop"


def norm(s: str) -> str:
    return re.sub(r"[^a-z0-9]", "", s.lower())


@dataclass
class LeanUnit:
    path: Path
    name: str
    doc: str = ""
    def_name: Optional[str] = None
    theorem_name: Optional[str] = None


def parse_lean_unit(path: Path) -> LeanUnit:
    text = path.read_text(encoding="utf-8", errors="ignore")
    # Extract first doc block between /-- and -/
    doc = ""
    m = re.search(r"/--(.*?)-/", text, flags=re.DOTALL)
    if m:
        doc_raw = m.group(1)
        # Clean common leading whitespace and Lean doc sigils
        lines = [ln.strip() for ln in doc_raw.splitlines()]
        doc = "\n".join([ln for ln in lines if ln])

    def_name = None
    thr_name = None
    # Find first def and theorem names (roughly)
    for ln in text.splitlines():
        if def_name is None:
            m1 = re.match(r"\s*def\s+([A-Za-z0-9_']+)", ln)
            if m1:
                def_name = m1.group(1)
        if thr_name is None:
            m2 = re.match(r"\s*theorem\s+([A-Za-z0-9_']+)", ln)
            if m2:
                thr_name = m2.group(1)
        if def_name and thr_name:
            break

    return LeanUnit(path=path, name=path.stem, doc=doc, def_name=def_name, theorem_name=thr_name)


def build_yaml_name_index(yaml_dir: Path) -> Dict[str, List[Path]]:
    idx: Dict[str, List[Path]] = {}
    for p in yaml_dir.glob("*.y*ml"):
        tail = p.stem.split("_")[-1]
        idx.setdefault(norm(tail), []).append(p)
    return idx


def find_yaml_match(lean_name: str, yaml_files: List[Path], idx_by_tail: Dict[str, List[Path]]) -> Optional[Path]:
    key = norm(lean_name)
    cands = list(idx_by_tail.get(key, []))
    if not cands:
        # fallback to substring search over normalized full name
        cands = [p for p in yaml_files if key in norm(p.stem)]
    if not cands:
        return None
    def score(p: Path) -> Tuple[int, int, int, str]:
        name = p.name
        s1 = 0 if name.startswith("Clover_") else 1
        s2 = 0 if key in norm(name.split("_")[-1]) else 1
        s3 = len(name)
        return (s1, s2, s3, name)
    cands.sort(key=score)
    return cands[0]


def make_yaml(unit: LeanUnit) -> str:
    """Emit YAML matching the Dafny deps-on-top schema (vc-spec/vc-code)."""
    desc = unit.doc.strip() if unit.doc.strip() else f"Lean translation of {unit.name} benchmark."
    def_sig = unit.def_name or unit.name
    thr_sig = unit.theorem_name or f"{unit.name}_spec"
    return f"""
vc-description: |-
  {desc}

vc-preamble: |-
  

vc-helpers: |-
  // <vc-helpers>
  // </vc-helpers>

vc-spec: |-
  // <vc-spec>
  -- def {def_sig} :=
  -- theorem {thr_sig} :=
  // </vc-spec>

vc-code: |-
  // <vc-code>
  {{- Lean implementation and proof go here -}}
  // </vc-code>

vc-postamble: |-
  -- Source: {unit.path.as_posix()}
""".lstrip()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="Actually write YAML files (default: dry run)")
    args = ap.parse_args()

    if not LEAN_SRC.is_dir():
        raise SystemExit(f"Missing Lean source dir: {LEAN_SRC}")
    if not DAFNY_YAML.is_dir():
        raise SystemExit(f"Missing Dafny yaml-depsontop dir: {DAFNY_YAML}")

    units = [parse_lean_unit(p) for p in sorted(LEAN_SRC.glob("*.lean"))]
    yaml_files = sorted(DAFNY_YAML.glob("*.y*ml"))
    idx_by_tail = build_yaml_name_index(DAFNY_YAML)

    LEAN_YAML_OUT.mkdir(parents=True, exist_ok=True)
    mapping_lines = ["lean_file,yaml_name"]
    missing: List[str] = []

    for u in units:
        match = find_yaml_match(u.name, yaml_files, idx_by_tail)
        if match is None:
            missing.append(u.name)
            continue
        out_path = LEAN_YAML_OUT / match.name
        mapping_lines.append(f"{u.path.name},{match.name}")
        content = make_yaml(u)
        if args.write:
            out_path.write_text(content, encoding="utf-8")

    # Write mapping and missing reports
    (LEAN_YAML_OUT / "mapping.csv").write_text("\n".join(mapping_lines) + "\n", encoding="utf-8")
    (LEAN_YAML_OUT / "unmatched.txt").write_text("\n".join(sorted(missing)) + "\n", encoding="utf-8")

    print(f"Matched {len(mapping_lines)-1} Lean files → {LEAN_YAML_OUT}")
    print(f"Unmatched: {len(missing)} (see unmatched.txt)")


if __name__ == "__main__":
    main()
