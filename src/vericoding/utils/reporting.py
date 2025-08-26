"""Summary and CSV generation utilities."""

import csv
from datetime import datetime
from pathlib import Path

from ..core.config import ProcessingConfig
from .git_utils import (
    get_git_remote_url,
    get_current_branch,
    get_github_url,
    get_repo_root,
)


def generate_csv_results(config: ProcessingConfig, results: list) -> str:
    """Generate CSV file with spec_name, spec_to_code, spec_link, and impl_link columns."""
    csv_file = Path(config.output_dir) / "results.csv"

    # Get repo info
    repo_url = get_git_remote_url() or ""
    branch = get_current_branch() or "main"
    repo_root = get_repo_root()

    with csv_file.open("w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(
            ["spec_name", "subfolder", "spec_to_code", "spec_link", "impl_link"]
        )
        # Write results
        for result in results:
            spec_name = str(
                Path(result.spec_yaml_file).with_suffix("")
            )  # Remove extension and preserve path
            spec_to_code = "SUCCESS" if result.success else "FAILED"

            # Extract subfolder
            file_path = Path(result.spec_yaml_file)
            subfolder = file_path.parts[0] if len(file_path.parts) > 1 else "root"

            # Generate spec link
            # result.file is already relative to config.files_dir, so construct the full path correctly
            spec_full_path = Path(config.files_dir) / result.spec_yaml_file
            try:
                spec_rel_path = spec_full_path.relative_to(Path(repo_root))
            except ValueError:
                # If the full path is not within repo_root, try to make it relative from current working directory
                try:
                    spec_rel_path = spec_full_path.relative_to(Path.cwd())
                except ValueError:
                    # If still not relative, use the path as-is
                    spec_rel_path = spec_full_path
            spec_link = (
                get_github_url(spec_rel_path, repo_url, branch) if repo_url else ""
            )

            # Generate impl link
            if result.code_file:
                try:
                    impl_rel_path = Path(result.code_file).relative_to(Path(repo_root))
                except ValueError:
                    # If the output path is not within repo_root, try to make it relative from current working directory
                    try:
                        impl_rel_path = Path(result.code_file).relative_to(Path.cwd())
                    except ValueError:
                        # If still not relative, use the path as-is
                        impl_rel_path = Path(result.code_file)
                impl_link = (
                    get_github_url(impl_rel_path, repo_url, branch) if repo_url else ""
                )
            else:
                impl_link = ""

            writer.writerow([spec_name, subfolder, spec_to_code, spec_link, impl_link])

    print(f"CSV results saved to: {csv_file}")
    return str(csv_file)


def generate_subfolder_analysis_csv(config: ProcessingConfig, results: list) -> str:
    """Generate CSV file with subfolder success rate analysis."""
    csv_file = Path(config.output_dir) / "subfolder_analysis.csv"

    # Analyze results by subfolder
    from collections import defaultdict

    subfolder_stats = defaultdict(lambda: {"success": 0, "failed": 0, "total": 0})

    for result in results:
        # Extract subfolder from file path
        file_path = Path(result.spec_yaml_file)
        if len(file_path.parts) > 1:
            subfolder = file_path.parts[0]
        else:
            subfolder = "root"

        subfolder_stats[subfolder]["total"] += 1
        if result.success:
            subfolder_stats[subfolder]["success"] += 1
        else:
            subfolder_stats[subfolder]["failed"] += 1

    with csv_file.open("w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(["subfolder", "successful", "failed", "total", "success_rate"])

        # Write subfolder statistics sorted by name
        for subfolder in sorted(subfolder_stats.keys()):
            stats = subfolder_stats[subfolder]
            success_rate = (
                (stats["success"] / stats["total"] * 100) if stats["total"] > 0 else 0.0
            )
            writer.writerow(
                [
                    subfolder,
                    stats["success"],
                    stats["failed"],
                    stats["total"],
                    f"{success_rate:.1f}%",
                ]
            )

    print(f"Subfolder analysis CSV saved to: {csv_file}")
    return str(csv_file)


def print_summary(config: ProcessingConfig, results: list, processing_time: float) -> str:
    """Generate and print processing summary with reports."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success]

    # Create simple summary
    summary_lines = [
        f"=== {config.language_config.name.upper()} PROCESSING SUMMARY ===",
        f"Total files: {len(results)}",
        f"Successful: {len(successful)} ({len(successful) / len(results) * 100:.1f}%)",
        f"Failed: {len(failed)}",
        f"Processing time: {processing_time:.2f}s",
        f"Average per file: {processing_time / len(results):.2f}s",
        "",
        "Successful files:",
    ]
    
    for result in successful:
        summary_lines.append(f"✓ {Path(result.spec_yaml_file).name}")
    
    if failed:
        summary_lines.extend(["", "Failed files:"])
        for result in failed:
            summary_lines.append(f"✗ {Path(result.spec_yaml_file).name}")

    summary = "\n".join(summary_lines)

    # Save summary to file
    with Path(config.summary_file).open("w") as f:
        f.write(summary)

    # Print to console
    print("")
    print(summary)
    print(f"\nSummary saved to: {config.summary_file}")
    print(f"Files saved to: {config.output_dir}")

    # Generate CSV reports
    generate_csv_results(config, results)
    generate_subfolder_analysis_csv(config, results)

    # Print final celebration
    print(f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful")
    print(f"⚡ Completed in {processing_time:.2f}s with {config.max_workers} workers")

    return summary
