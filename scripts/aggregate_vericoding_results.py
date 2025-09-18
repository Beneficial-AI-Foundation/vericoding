#!/usr/bin/env python3
import csv
import re
import argparse
from pathlib import Path
from typing import Dict, List, Set, Tuple


def _parse_run_timestamp(name: str) -> Tuple[int, int, int, int]:
    """Parse run folder timestamp suffix like _MM-DD_HHhMM -> (MM, DD, HH, MM)."""
    m = re.search(r"_(\d{2})-(\d{2})_(\d{2})h(\d{2})$", name)
    if not m:
        return (0, 0, 0, 0)
    return tuple(int(x) for x in m.groups())  # type: ignore[return-value]


def calculate_success_rate(run_dir: Path) -> float:
    """
    Calculate success rate for a run by parsing summary.txt or results.csv.
    Returns success rate as a float between 0.0 and 1.0.
    """
    # Try both directory structures: dafny/ subdir and direct
    results_csv = run_dir / "dafny" / "results.csv"
    if not results_csv.exists():
        results_csv = run_dir / "results.csv"
    
    if results_csv.exists():
        successes, failures = parse_results_statuses(results_csv)
        total = len(successes) + len(failures)
        return len(successes) / total if total > 0 else 0.0
    
    # Fallback to summary.txt
    summary_txt = run_dir / "dafny" / "summary.txt"
    if not summary_txt.exists():
        summary_txt = run_dir / "summary.txt"
    
    if summary_txt.exists():
        # Try to extract success rate directly from summary statistics
        text = summary_txt.read_text(encoding="utf-8", errors="ignore")
        
        # Look for explicit success rate in summary
        rate_match = re.search(r"Success rate:\s*([\d.]+)%", text)
        if rate_match:
            return float(rate_match.group(1)) / 100.0
            
        # Look for explicit totals
        total_match = re.search(r"Total original files:\s*(\d+)", text)
        success_match = re.search(r"Total successful:\s*(\d+)", text)
        if total_match and success_match:
            total = int(total_match.group(1))
            successful = int(success_match.group(1))
            return successful / total if total > 0 else 0.0
        
        # Fallback to parsing individual files
        successes = parse_summary_successes(summary_txt)
        failures = parse_summary_failures(summary_txt)
        total = len(successes) + len(failures)
        return len(successes) / total if total > 0 else 0.0
    
    return 0.0


def find_latest_llm_runs(bignum_root: Path) -> Dict[str, Path]:
    """
    Return mapping from LLM name to latest run directory under bignum_root.
    Expects subdirs like: vericoder_<llm>_MM-DD_HHhMM and uses directory mtime.
    """
    latest: Dict[str, Tuple[Path, float]] = {}
    for p in bignum_root.iterdir():
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
        prev = latest.get(llm)
        if prev is None or ts > prev[1]:
            latest[llm] = (p, ts)
    return {llm: path for llm, (path, _) in latest.items()}


def find_best_llm_runs(bignum_root: Path) -> Dict[str, Path]:
    """
    Return mapping from LLM name to best (highest success rate) run directory under bignum_root.
    Expects subdirs like: vericoder_<llm>_MM-DD_HHhMM.
    """
    best: Dict[str, Tuple[Path, float]] = {}
    for p in bignum_root.iterdir():
        if not p.is_dir():
            continue
        name = p.name
        if not name.startswith("vericoder_"):
            continue
        parts = name.split("_")
        if len(parts) < 3:
            continue
        llm = parts[1]
        success_rate = calculate_success_rate(p)
        prev = best.get(llm)
        if prev is None or success_rate > prev[1]:
            best[llm] = (p, success_rate)
    return {llm: path for llm, (path, _) in best.items()}


def parse_summary_successes(summary_path: Path) -> Set[str]:
    """
    Parse summary.txt and return set of successful file basenames without extension.
    Looks for sections like:
      Successful files:\n
      ✓ filename.rs (for Verus)
      ✓ filename.dfy (for Dafny)
    Or W&B format:
      === SUCCESSFUL FILES (VERIFIED) ===
      ✓ filename -> filename_impl.rs
    """
    successes: Set[str] = set()
    if not summary_path.exists():
        return successes
    text = summary_path.read_text(encoding="utf-8", errors="ignore")
    
    # Try standard format first
    m = re.search(r"Successful files:\n([\s\S]*?)\nFailed files:\n", text)
    block = None
    if m:
        block = m.group(1)
    else:
        m2 = re.search(r"Successful files:\n([\s\S]*)$", text)
        if m2:
            block = m2.group(1)
    
    # Try W&B format if standard format not found
    if block is None:
        m3 = re.search(r"=== SUCCESSFUL FILES \(VERIFIED\) ===\n([\s\S]*?)\n=== FAILED FILES", text)
        if m3:
            block = m3.group(1)
    
    if block is None:
        return successes
        
    for raw in block.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("✓ "):
            line = line[2:].strip()
            
        # Handle different formats:
        # Standard: "filename.rs" (Verus) or "filename.dfy" (Dafny)
        # W&B: "filename -> filename_impl.rs"
        if " -> " in line:
            # W&B format: extract base name before " -> "
            base_name = line.split(" -> ")[0].strip()
            successes.add(base_name)
        elif line.endswith(".rs"):
            successes.add(line[:-3])
        elif line.endswith(".dfy"):
            successes.add(line[:-4])
        else:
            # No extension, add as-is (backward compatibility)
            successes.add(line)
    return successes


def parse_results_successes(results_csv: Path) -> Set[str]:
    """Parse results.csv and return set of successful file basenames (no extension).

    results.csv columns: spec_name, subfolder, spec_to_code, spec_link, impl_link
    spec_name appears to be a path like
      benchmarks/dafny/bignum/yaml/bignum_CompareUnequal (no extension)
    """
    successes: Set[str] = set()
    if not results_csv.exists():
        return successes
    with results_csv.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if (row.get("spec_to_code") or "").strip().upper() == "SUCCESS":
                spec_name = (row.get("spec_name") or "").strip()
                if not spec_name:
                    continue
                base = Path(spec_name).name  # already without extension
                successes.add(base)
    return successes


def parse_results_statuses(results_csv: Path) -> Tuple[Set[str], Set[str]]:
    """Parse results.csv and return (successes, failures) as basenames without extension."""
    successes: Set[str] = set()
    failures: Set[str] = set()
    if not results_csv.exists():
        return successes, failures
    with results_csv.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            status = (row.get("spec_to_code") or "").strip().upper()
            spec_name = (row.get("spec_name") or "").strip()
            if not spec_name:
                continue
            base = Path(spec_name).name
            if not base:
                continue
            if status == "SUCCESS":
                successes.add(base)
            elif status:
                failures.add(base)
    return successes, failures


def parse_summary_failures(summary_path: Path) -> Set[str]:
    """Parse summary.txt and return set of failed file basenames without extension."""
    fails: Set[str] = set()
    if not summary_path.exists():
        return fails
    text = summary_path.read_text(encoding="utf-8", errors="ignore")
    
    # Try standard format first
    m = re.search(r"Failed files:\n([\s\S]*)", text)
    if not m:
        # Try W&B format
        m = re.search(r"=== FAILED FILES \(VERIFICATION\) ===\n([\s\S]*)", text)
    
    if not m:
        return fails
        
    for raw in m.group(1).splitlines():
        line = raw.strip()
        if not line or line.startswith("===") or "All remaining" in line:
            continue
        if line.startswith("✗ "):
            fname = line[2:].strip()
            if fname.endswith(".rs"):
                fails.add(fname[:-3])
            elif fname.endswith(".dfy"):
                fails.add(fname[:-4])
            else:
                # No extension, add as-is (backward compatibility)
                fails.add(fname)
    return fails


def collect_all_files(latest_runs: Dict[str, Path]) -> Set[str]:
    """Build superset of all filenames (without extension) across successes and failures.

    Prefer results.csv for coverage; fall back to summary.txt for failures if needed.
    """
    all_files: Set[str] = set()
    for _, run_dir in latest_runs.items():
        # Try both directory structures: dafny/ subdir and direct
        results_csv = run_dir / "dafny" / "results.csv"
        if not results_csv.exists():
            results_csv = run_dir / "results.csv"
        
        if results_csv.exists():
            with results_csv.open(newline="", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    spec_name = (row.get("spec_name") or "").strip()
                    if not spec_name:
                        continue
                    base = Path(spec_name).name
                    if base:
                        all_files.add(base)
        else:
            # Fallback to summary.txt
            summary = run_dir / "dafny" / "summary.txt"
            if not summary.exists():
                summary = run_dir / "summary.txt"
            if not summary.exists():
                continue
            text = summary.read_text(encoding="utf-8", errors="ignore")
            # successes
            all_files.update(parse_summary_successes(summary))
            # failures
            for base in parse_summary_failures(summary):
                all_files.add(base)
    return all_files


def main() -> int:
    parser = argparse.ArgumentParser(description="Aggregate Dafny vericoder runs")
    parser.add_argument(
        "--root",
        type=str,
        default=None,
        help="Root benchmark directory (e.g., benchmarks/verus/bignum or benchmarks/dafny/humaneval)",
    )
    parser.add_argument(
        "--best",
        action="store_true",
        help="Select runs with best success rate instead of latest runs for each LLM",
    )
    args = parser.parse_args()

    if args.root:
        bench_root = Path(args.root).resolve()
    else:
        # Default to bignum
        repo_root = Path(__file__).resolve().parents[1]
        bench_root = repo_root / "benchmarks" / "dafny" / "bignum"
    if not bench_root.exists():
        print(f"ERROR: root not found: {bench_root}")
        return 1

    # Detect language based on path (dafny vs verus)
    is_verus = "verus" in bench_root.parts
    # For Dafny benchmarks, some suites (e.g. verina) use .dfy specs directly,
    # while others (e.g. dafnybench) use .yaml. Try a list of candidates.
    spec_ext_candidates = [".rs"] if is_verus else [".yaml", ".dfy"]
    # Choose an impl extension based on language
    impl_ext = ".rs" if is_verus else ".dfy"

    if args.best:
        selected_runs = find_best_llm_runs(bench_root)
        selection_method = "best"
    else:
        selected_runs = find_latest_llm_runs(bench_root)
        selection_method = "latest"
    
    if not selected_runs:
        print("No vericoder runs found.")
        return 0

    # Ensure an output root folder to collect all artifacts
    results_root = bench_root / "vericoding-results"
    results_root.mkdir(parents=True, exist_ok=True)

    # successes/failures per llm (union of results.csv and summary.txt lists)
    llm_successes: Dict[str, Set[str]] = {}
    llm_failures: Dict[str, Set[str]] = {}
    for llm, run_dir in selected_runs.items():
        successes: Set[str] = set()
        failures: Set[str] = set()
        # Try both directory structures: dafny/ subdir and direct
        results_csv = run_dir / "dafny" / "results.csv"
        if not results_csv.exists():
            results_csv = run_dir / "results.csv"
        succ_rs, fail_rs = parse_results_statuses(results_csv)
        successes |= succ_rs
        failures |= fail_rs
        
        summary_txt = run_dir / "dafny" / "summary.txt"
        if not summary_txt.exists():
            summary_txt = run_dir / "summary.txt"
        successes |= parse_summary_successes(summary_txt)
        failures |= parse_summary_failures(summary_txt)
        llm_successes[llm] = successes
        llm_failures[llm] = failures

    # Use canonical file list from the benchmark directory instead of collecting from runs
    # This ensures we only include the official test files, not extras from W&B runs
    files_dir = bench_root / "files"
    chosen_spec_ext = None
    if files_dir.exists():
        all_files = set()
        # Try each candidate extension until we find any files
        for cand in spec_ext_candidates:
            matched = list(files_dir.glob(f"*{cand}"))
            if matched:
                for f in matched:
                    base_name = f.stem  # filename without extension
                    all_files.add(base_name)
                chosen_spec_ext = cand
                break
        # If nothing matched (e.g., unexpected layout), fallback to collecting from runs
        if not all_files:
            all_files = collect_all_files(selected_runs)
            # Best-effort default for printing extensions
            chosen_spec_ext = spec_ext_candidates[-1] if spec_ext_candidates else ""
    else:
        # Fallback to collecting from runs if no files/ directory
        all_files = collect_all_files(selected_runs)
        chosen_spec_ext = spec_ext_candidates[-1] if spec_ext_candidates else ""

    # Aggregate rows and file->llms mapping
    rows: List[Tuple[str, str, int, str]] = []
    file_to_llms: Dict[str, List[str]] = {}
    for filename in sorted(all_files):
        successful_llms = sorted([llm for llm, s in llm_successes.items() if filename in s])
        file_to_llms[filename] = successful_llms
        success_count = len(successful_llms)
        success_status = "SUCCESS" if success_count > 0 else "FAILED"
        rows.append((filename, success_status, success_count, ", ".join(successful_llms)))

    out_csv = results_root / "vericoding_aggregate.csv"
    with out_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["filename", "success_status", "total_llms", "successful_llms"])
        for r in rows:
            w.writerow(r)

    print(
        f"Wrote {out_csv} with {len(rows)} rows from {len(llm_successes)} {selection_method} LLM runs"
    )

    # Write union-summary.txt similar to per-LLM summary, but aggregated
    summary_path = results_root / "union-summary.txt"
    total_files = len(all_files)
    successful_files = [f for f, llms in file_to_llms.items() if llms]
    failed_files = [f for f, llms in file_to_llms.items() if not llms]
    with summary_path.open("w", encoding="utf-8") as sf:
        sf.write(f"=== {'VERUS' if is_verus else 'DAFNY'} PROCESSING SUMMARY (AGGREGATED) ===\n")
        sf.write(f"Selection method: {selection_method} runs\n")
        sf.write(f"Total files: {total_files}\n")
        sf.write(f"Successful: {len(successful_files)} ({(100.0*len(successful_files)/total_files if total_files else 0):.1f}%)\n")
        sf.write(f"Failed: {len(failed_files)}\n")
        # Selected runs information
        if selected_runs:
            sf.write("\n")
            sf.write(f"Selected {selection_method} runs:\n")
            for llm in sorted(selected_runs.keys()):
                run_dir = selected_runs[llm]
                if args.best:
                    success_rate = calculate_success_rate(run_dir)
                    sf.write(f"  - {llm}: {run_dir.name} (success rate: {success_rate:.1%})\n")
                else:
                    sf.write(f"  - {llm}: {run_dir.name}\n")
        
        # Per-LLM success rates over the union of files in this benchmark
        if llm_successes:
            sf.write("\n")
            sf.write("Per-LLM success rates:\n")
            for llm in sorted(llm_successes.keys()):
                succ_count = len(llm_successes[llm].intersection(all_files))
                rate = (100.0 * succ_count / total_files) if total_files else 0.0
                sf.write(f"  - {llm}: {succ_count}/{total_files} ({rate:.1f}%)\n")
        sf.write("\n")
        sf.write("Successful files:\n")
        for f in sorted(successful_files):
            llms = ", ".join(file_to_llms[f])
            ext = chosen_spec_ext or (".rs" if is_verus else ".dfy")
            sf.write(f"✓ {f}{ext} — by: {llms}\n")
        sf.write("\n")
        sf.write("Failed files:\n")
        for f in sorted(failed_files):
            ext = chosen_spec_ext or (".rs" if is_verus else ".dfy")
            sf.write(f"✗ {f}{ext}\n")

    # Copy all successful implementations into success folder with per-file index prefix and LLM suffix
    success_dir = results_root / "success"
    success_dir.mkdir(parents=True, exist_ok=True)

    # Assign stable index per successful filename
    file_index: Dict[str, int] = {fname: i for i, fname in enumerate(sorted(successful_files), start=1)}

    for filename in sorted(successful_files):
        idx = file_index[filename]
        for llm in sorted(file_to_llms.get(filename, [])):
            # Find source file in that llm's selected run
            run_dir = selected_runs.get(llm)
            if run_dir is None:
                continue
            # Try both directory structures and file naming patterns
            src_file = (run_dir / "dafny" / f"{filename}_impl{impl_ext}")
            if not src_file.exists():
                src_file = run_dir / f"{filename}_impl{impl_ext}"
            if not src_file.exists():
                continue
            dest_file = success_dir / f"{idx}_{filename}_impl_{llm}{impl_ext}"
            try:
                content = src_file.read_bytes()
                if not dest_file.exists() or dest_file.read_bytes() != content:
                    dest_file.write_bytes(content)
            except Exception as e:
                print(f"WARN: Failed to copy {src_file} -> {dest_file}: {e}")

    # Copy all failed implementations into failed using the same naming convention
    failed_dir = results_root / "failed"
    failed_dir.mkdir(parents=True, exist_ok=True)

    file_index_failed: Dict[str, int] = {fname: i for i, fname in enumerate(sorted(failed_files), start=1)}

    for filename in sorted(failed_files):
        idx = file_index_failed[filename]
        # LLMs that failed this filename
        failed_llms = sorted([llm for llm, s in llm_failures.items() if filename in s])
        for llm in failed_llms:
            run_dir = selected_runs.get(llm)
            if run_dir is None:
                continue
            src_file = (run_dir / "dafny" / f"{filename}_impl{impl_ext}")
            if not src_file.exists():
                src_file = run_dir / f"{filename}_impl{impl_ext}"
            if not src_file.exists():
                continue
            dest_file = failed_dir / f"{idx}_{filename}_impl_{llm}{impl_ext}"
            try:
                content = src_file.read_bytes()
                if not dest_file.exists() or dest_file.read_bytes() != content:
                    dest_file.write_bytes(content)
            except Exception as e:
                print(f"WARN: Failed to copy {src_file} -> {dest_file}: {e}")

    print(f"Wrote {summary_path} and copied successes into {success_dir} and failures into {failed_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


