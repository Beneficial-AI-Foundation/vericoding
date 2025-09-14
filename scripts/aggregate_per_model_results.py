#!/usr/bin/env python3
import csv
import re
import argparse
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


def _parse_run_timestamp(name: str) -> Tuple[int, int, int, int]:
    """Parse run folder timestamp suffix like _MM-DD_HHhMM -> (MM, DD, HH, MM)."""
    m = re.search(r"_(\d{2})-(\d{2})_(\d{2})h(\d{2})$", name)
    if not m:
        return (0, 0, 0, 0)
    return tuple(int(x) for x in m.groups())  # type: ignore[return-value]


def find_latest_run_per_model_per_benchmark(root: Path) -> Dict[str, List[Tuple[str, Path]]]:
    """
    For each benchmark subdirectory under `root`, pick the latest run for each model.
    Returns mapping model -> list of (benchmark_name, latest_run_dir) per benchmark where present.
    """
    model_to_runs: Dict[str, List[Tuple[str, Path]]] = {}
    for bench_dir in root.iterdir():
        if not bench_dir.is_dir():
            continue
        # Track latest per model within this benchmark directory
        latest_in_bench: Dict[str, Tuple[Path, Tuple[int, int, int, int]]] = {}
        for p in bench_dir.iterdir():
            if not p.is_dir():
                continue
            name = p.name
            if not name.startswith("vericoder_"):
                continue
            parts = name.split("_")
            if len(parts) < 3:
                continue
            llm = parts[1]
            ts = _parse_run_timestamp(name)
            prev = latest_in_bench.get(llm)
            if prev is None or ts > prev[1]:
                latest_in_bench[llm] = (p, ts)
        # Append the latest runs from this benchmark to global mapping
        bench_name = bench_dir.name
        for llm, (path, _) in latest_in_bench.items():
            model_to_runs.setdefault(llm, []).append((bench_name, path))
    return model_to_runs


def parse_results_success_fail_counts(results_csv: Path) -> Tuple[int, int, int]:
    """Return (total_files, num_successes, num_failures) from a results.csv file."""
    total = 0
    succ = 0
    fail = 0
    if not results_csv.exists():
        return (0, 0, 0)
    with results_csv.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            status = (row.get("spec_to_code") or "").strip().upper()
            if status:
                total += 1
                if status == "SUCCESS":
                    succ += 1
                else:
                    fail += 1
    return (total, succ, fail)


def parse_summary_counts(summary_path: Path) -> Tuple[int, int, int]:
    """Fallback counts from a summary.txt file. Return (total, successes, failures)."""
    if not summary_path.exists():
        return (0, 0, 0)
    text = summary_path.read_text(encoding="utf-8", errors="ignore")
    # Try to parse lines:
    # Total original files: X
    # Total successful: Y
    # Total failed: Z
    def _extract_int(pattern: str) -> Optional[int]:
        m = re.search(pattern, text)
        if m:
            try:
                return int(m.group(1))
            except Exception:
                return None
        return None

    total = _extract_int(r"Total original files:\s*(\d+)")
    succ = _extract_int(r"Total successful:\s*(\d+)")
    fail = _extract_int(r"Total failed:\s*(\d+)")
    if total is None or succ is None or fail is None:
        # Fallback: count checkmarks and crosses
        succ = len(re.findall(r"^\s*✓\s", text, flags=re.M)) if succ is None else succ
        fail = len(re.findall(r"^\s*✗\s", text, flags=re.M)) if fail is None else fail
        total = (succ or 0) + (fail or 0) if total is None else total
    return (total or 0, succ or 0, fail or 0)


def get_run_counts(run_dir: Path) -> Tuple[int, int, int]:
    """Get (total, success, fail) for a single run directory, from results.csv or summary.txt."""
    # Try both directory structures: dafny subdir and direct
    results_csv = run_dir / "dafny" / "results.csv"
    if not results_csv.exists():
        results_csv = run_dir / "results.csv"
    if results_csv.exists():
        return parse_results_success_fail_counts(results_csv)

    summary = run_dir / "dafny" / "summary.txt"
    if not summary.exists():
        summary = run_dir / "summary.txt"
    return parse_summary_counts(summary)


def main() -> int:
    parser = argparse.ArgumentParser(description="Aggregate per-model Dafny vericoder results across benchmarks")
    parser.add_argument(
        "--root",
        type=str,
        default=None,
        help="Root directory containing Dafny benchmarks (e.g., benchmarks/dafny)",
    )
    args = parser.parse_args()

    if args.root:
        root = Path(args.root).resolve()
    else:
        root = (Path(__file__).resolve().parents[1] / "benchmarks" / "dafny").resolve()
    if not root.exists():
        print(f"ERROR: root not found: {root}")
        return 1

    model_to_runs = find_latest_run_per_model_per_benchmark(root)
    if not model_to_runs:
        print("No vericoder runs found under root.")
        return 0

    # Aggregate per model across benchmarks (summing their latest runs per benchmark)
    rows: List[Tuple[str, int, int, int, float, str]] = []
    # columns: model, total_files, successes, failures, success_rate_pct, run_paths_semicolon
    per_benchmark_rows: List[Tuple[str, str, int, int, int, float, str]] = []
    # columns: model, benchmark, total_files, successes, failures, success_rate_pct, run_path

    # For TOTAL (union coverage across all models): track union of filenames and union of successes per benchmark
    bench_to_union_all: Dict[str, Set[str]] = {}
    bench_to_union_success: Dict[str, Set[str]] = {}

    def parse_results_names(results_csv: Path) -> Tuple[Set[str], Set[str]]:
        """Return (all_files, success_files) basenames from results.csv."""
        all_files: Set[str] = set()
        success_files: Set[str] = set()
        if not results_csv.exists():
            return all_files, success_files
        with results_csv.open(newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                spec_name = (row.get("spec_name") or "").strip()
                if not spec_name:
                    continue
                base = Path(spec_name).name
                if not base:
                    continue
                all_files.add(base)
                if (row.get("spec_to_code") or "").strip().upper() == "SUCCESS":
                    success_files.add(base)
        return all_files, success_files

    for llm in sorted(model_to_runs.keys()):
        totals = succs = fails = 0
        paths: List[str] = []
        for bench_name, run_dir in model_to_runs[llm]:
            t, s, f = get_run_counts(run_dir)
            totals += t
            succs += s
            fails += f
            path_str = str(run_dir)
            paths.append(path_str)
            rate_b = (100.0 * s / t) if t else 0.0
            per_benchmark_rows.append((llm, bench_name, t, s, f, rate_b, path_str))

            # Update union coverage via results.csv if available
            res_csv = run_dir / "dafny" / "results.csv"
            if not res_csv.exists():
                res_csv = run_dir / "results.csv"
            all_names, succ_names = parse_results_names(res_csv)
            if all_names:
                bench_to_union_all.setdefault(bench_name, set()).update(all_names)
            if succ_names:
                bench_to_union_success.setdefault(bench_name, set()).update(succ_names)
        rate = (100.0 * succs / totals) if totals else 0.0
        rows.append((llm, totals, succs, fails, rate, ";".join(paths)))

    out_csv = root / "vericoding_per_model_aggregate.csv"
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["model", "total_files", "successes", "failures", "success_rate_pct", "run_paths"])
        for r in rows:
            w.writerow(r)
        # TOTAL row across all models (union coverage): sum over benchmarks of unique files
        grand_total = sum(len(s) for s in bench_to_union_all.values())
        grand_succ = sum(len(s) for s in bench_to_union_success.values())
        grand_fail = max(grand_total - grand_succ, 0)
        grand_rate = (100.0 * grand_succ / grand_total) if grand_total else 0.0
        w.writerow(["TOTAL", grand_total, grand_succ, grand_fail, f"{grand_rate:.1f}", ""]) 

    # Per-benchmark CSV
    per_bench_csv = root / "vericoding_per_model_per_benchmark.csv"
    with per_bench_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["model", "benchmark", "total_files", "successes", "failures", "success_rate_pct", "run_path"])
        for r in sorted(per_benchmark_rows, key=lambda x: (x[0], x[1])):
            w.writerow(r)

    # Human-readable summary
    summary_path = root / "per-model-union-summary.txt"
    with summary_path.open("w", encoding="utf-8") as sf:
        sf.write("=== DAFNY PER-MODEL PROCESSING SUMMARY (AGGREGATED ACROSS BENCHMARKS) ===\n")
        sf.write(f"Root: {root}\n")
        sf.write(f"Models found: {len(rows)}\n\n")
        for llm, total, succ, fail, rate, paths in sorted(rows, key=lambda x: x[0]):
            sf.write(f"Model: {llm}\n")
            sf.write(f"  Overall: total={total}, success={succ}, fail={fail}, rate={rate:.1f}%\n")
            sf.write("  Per-benchmark:\n")
            for m, bench, t, s, f, rb, path in sorted(per_benchmark_rows, key=lambda x: (x[0], x[1])):
                if m != llm:
                    continue
                sf.write(f"    - {bench:<14} total={t:<4} success={s:<4} fail={f:<4} rate={rb:>5.1f}%  path={path}\n")
            sf.write("\n")
        # TOTAL block (union coverage across models per benchmark)
        grand_total = sum(len(s) for s in bench_to_union_all.values())
        grand_succ = sum(len(s) for s in bench_to_union_success.values())
        grand_fail = max(grand_total - grand_succ, 0)
        grand_rate = (100.0 * grand_succ / grand_total) if grand_total else 0.0
        sf.write("TOTAL:\n")
        sf.write(f"  Overall: total={grand_total}, success={grand_succ}, fail={grand_fail}, rate={grand_rate:.1f}%\n")

    print(
        f"Wrote {out_csv}, {per_bench_csv} and {summary_path} with {len(rows)} models aggregated (latest per benchmark)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


