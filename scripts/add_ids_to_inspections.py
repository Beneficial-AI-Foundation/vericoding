#!/usr/bin/env python3
"""Add ID fields to analysis.yaml files based on benchmark jsonl files."""

import json
import re
import yaml
from pathlib import Path

# Mapping from inspection folder to (benchmark jsonl path, id prefix)
BENCHMARK_MAPPING = {
    # Dafny
    ("dafny", "apps"): ("benchmarks/dafny/apps/dafny_apps.jsonl", "DA"),
    ("dafny", "dafnybench"): ("benchmarks/dafny/dafnybench/dafny_dafnybench.jsonl", "DD"),
    ("dafny", "humaneval"): ("benchmarks/dafny/humaneval/dafny_humaneval.jsonl", "DH"),
    ("dafny", "verified-cogen"): ("benchmarks/dafny/verified_cogen/dafny_verified_cogen.jsonl", "DJ"),
    ("dafny", "verina"): ("benchmarks/dafny/verina/dafny_verina.jsonl", "DV"),
    ("dafny", "bignum"): ("benchmarks/dafny/bignum/dafny_bignum.jsonl", "DB"),
    # Lean
    ("lean", "dafnybench"): ("benchmarks/lean/dafnybench/lean_dafnybench.jsonl", "LD"),
    ("lean", "appstest"): ("benchmarks/lean/apps/lean_apps.jsonl", "LA"),
    ("lean", "bignum"): ("benchmarks/lean/bignum/lean_bignum.jsonl", "LB"),
    ("lean", "numpys"): ("benchmarks/lean/numpy_simple/lean_numpy_simple.jsonl", "LS"),
    ("lean", "verina"): ("benchmarks/lean/verina/lean_verina.jsonl", "LV"),
    ("lean", "verifcogen"): ("benchmarks/lean/verified_cogen/lean_verified_cogen.jsonl", "LJ"),
    ("lean", "numpy3"): ("benchmarks/lean/numpy_triple/lean_numpy_triple.jsonl", "LT"),
    # lean/humaneval maps to clever benchmark: HumanEval_X -> clever_X
    # Clever is derived from HumanEval with problems 22, 137, 162 missing (see benchmarks/README.md)
    ("lean", "humaneval"): ("benchmarks/lean/clever/lean_clever.jsonl", "LC"),
    # Verus
    ("verus", "humaneval"): ("benchmarks/verus/humaneval/verus_humaneval.jsonl", "VH"),
    ("verus", "verified-cogen"): ("benchmarks/verus/verified_cogen/verus_verified_cogen.jsonl", "VJ"),
    ("verus", "verina"): ("benchmarks/verus/verina/verus_verina.jsonl", "VV"),
    ("verus", "bignum"): ("benchmarks/verus/bignum/verus_bignum.jsonl", "VB"),
    ("verus", "numpy_triple"): ("benchmarks/verus/numpy_triple/verus_numpy_triple.jsonl", "VT"),
}


def extract_source_id(filename: str, language: str, benchmark: str) -> list[str]:
    """Extract possible source_id candidates from a sampled filename."""
    # Remove extension
    if filename.endswith(".dfy"):
        base = filename[:-4]
    elif filename.endswith(".lean"):
        base = filename[:-5]
    elif filename.endswith(".rs"):
        base = filename[:-3]
    else:
        base = filename

    # Remove leading experiment number (e.g., "152_")
    base = re.sub(r"^\d+_", "", base)

    # Remove trailing _impl_<model> pattern
    base = re.sub(r"_impl_[a-zA-Z0-9-]+$", "", base)

    candidates = [base]

    # HumanEval: "152-compare" -> "humaneval_152" or "humaneval_152_compare"
    if benchmark == "humaneval":
        # Pattern: XXX-name or XXX_name where XXX is a number
        m = re.match(r"(\d+)[-_](.+)", base)
        if m:
            num, name = m.groups()
            name = name.replace("-", "_")
            candidates.extend([
                f"humaneval_{num}",
                f"humaneval_{num}_{name}",
                f"humaneval_{int(num):03d}",
                f"humaneval_{int(num):03d}_{name}",
                # Handle patterns like "070-strange_sort_list" -> "humaneval_070_strange_sort_list__strange_sort_list_helper"
                f"humaneval_{int(num):03d}_{name}__{name}_helper",
            ])
        # For lean humaneval -> clever mapping: HumanEval_XX -> clever_XX
        m2 = re.match(r"HumanEval_(\d+)", base)
        if m2:
            num = int(m2.group(1))
            candidates.extend([
                f"clever_{num}",
            ])

    # BigNum: "bignums_X" -> "bignum_X", handle brackets
    if benchmark == "bignum":
        # Fix bignums -> bignum
        if base.startswith("bignums_"):
            candidates.append("bignum_" + base[8:])
        # Handle brackets: bignum_ModExp[Add,Mul,Zeroes] -> bignum_ModExp_Add_Mul_Zeroes
        bracket_match = re.match(r"(.+?)\[([^\]]+)\]", base)
        if bracket_match:
            prefix, bracket_content = bracket_match.groups()
            # Remove commas from bracket content
            parts = bracket_content.replace(",", "_")
            candidates.append(f"{prefix}_{parts}")
        # For Lean bignum: "ModExp_int" -> "bignum_ModExp" etc.
        if language == "lean":
            # Remove _int suffix if present
            cleaned = re.sub(r"_int$", "", base)
            candidates.append(f"bignum_{cleaned}")

    # Dafnybench: handle spaces in path names
    if benchmark == "dafnybench":
        # Replace spaces with underscores
        candidates.append(base.replace(" ", "_"))

    return candidates


def load_source_id_index(jsonl_path: Path) -> dict[str, int]:
    """Load jsonl and create source_id -> line_number mapping."""
    index = {}
    with open(jsonl_path) as f:
        for line_num, line in enumerate(f):
            data = json.loads(line)
            source_id = data.get("source_id", "")
            index[source_id] = line_num  # 0-indexed (matches ID format)
    return index


def process_analysis_yaml(yaml_path: Path, root: Path):
    """Process a single analysis.yaml file."""
    # Determine language and benchmark from path
    parts = yaml_path.relative_to(root / "experiments" / "inspection").parts
    language = parts[0]  # dafny, lean, verus
    benchmark = parts[1]  # apps, humaneval, etc.

    key = (language, benchmark)
    if key not in BENCHMARK_MAPPING:
        print(f"Warning: No mapping for {key}")
        return False

    jsonl_rel_path, prefix = BENCHMARK_MAPPING[key]
    if jsonl_rel_path is None:
        print(f"Warning: No jsonl file for {key}")
        return False

    jsonl_path = root / jsonl_rel_path
    if not jsonl_path.exists():
        print(f"Warning: jsonl file not found: {jsonl_path}")
        return False

    # Load source_id index
    source_id_index = load_source_id_index(jsonl_path)

    # Read analysis.yaml
    with open(yaml_path) as f:
        data = yaml.safe_load(f)

    # Process each sampled file
    modified = False
    for entry in data.get("files-sampled", []):
        filename = entry.get("file", "")
        candidates = extract_source_id(filename, language, benchmark)

        found = False
        for source_id in candidates:
            if source_id in source_id_index:
                line_num = source_id_index[source_id]
                entry["id"] = f"{prefix}{line_num:04d}"
                modified = True
                found = True
                print(f"  {filename} -> {source_id} -> {entry['id']}")
                break

        if not found:
            print(f"  Warning: source_id not found: {candidates[0]} (from {filename})")

    # Write back
    if modified:
        with open(yaml_path, "w") as f:
            yaml.dump(data, f, default_flow_style=False, allow_unicode=True, sort_keys=False)

    return modified


def main():
    root = Path(__file__).parent.parent
    inspection_dir = root / "experiments" / "inspection"

    yaml_files = list(inspection_dir.glob("**/analysis.yaml"))
    print(f"Found {len(yaml_files)} analysis.yaml files")

    for yaml_path in sorted(yaml_files):
        print(f"\nProcessing: {yaml_path.relative_to(root)}")
        process_analysis_yaml(yaml_path, root)


if __name__ == "__main__":
    main()
