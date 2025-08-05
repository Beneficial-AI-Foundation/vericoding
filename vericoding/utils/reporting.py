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
        writer.writerow(["spec_name", "spec_to_code", "spec_link", "impl_link"])
        # Write results
        for result in results:
            spec_name = str(
                Path(result.file).with_suffix("")
            )  # Remove extension and preserve path
            spec_to_code = "SUCCESS" if result.success else "FAILED"

            # Generate spec link
            # result.file is already relative to config.files_dir, so construct the full path correctly
            spec_full_path = Path(config.files_dir) / result.file
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
            if result.output:
                try:
                    impl_rel_path = Path(result.output).relative_to(Path(repo_root))
                except ValueError:
                    # If the output path is not within repo_root, try to make it relative from current working directory
                    try:
                        impl_rel_path = Path(result.output).relative_to(Path.cwd())
                    except ValueError:
                        # If still not relative, use the path as-is
                        impl_rel_path = Path(result.output)
                impl_link = (
                    get_github_url(impl_rel_path, repo_url, branch) if repo_url else ""
                )
            else:
                impl_link = ""

            writer.writerow([spec_name, spec_to_code, spec_link, impl_link])

    print(f"CSV results saved to: {csv_file}")
    return str(csv_file)


def generate_summary(config: ProcessingConfig, results: list) -> str:
    """Generate a summary of the processing results."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success]

    summary_lines = [
        f"=== {config.language_config.name.upper()} SPECIFICATION-TO-CODE PROCESSING SUMMARY (PARALLEL VERSION) ===",
        "",
        f"Language: {config.language_config.name}",
        f"LLM Provider: {config.llm_provider}",
        f"LLM Model: {config.llm_model or 'default'}",
        f"Test directory: {config.files_dir}",
        f"Output directory: {config.output_dir}",
        f"Max iterations: {config.max_iterations}",
        f"Parallel workers: {config.max_workers}",
        f"Test date: {datetime.now().isoformat()}",
        "",
        f"Total original files: {len(results)}",
        "",
        "=== OVERALL STATISTICS ===",
        f"Total successful: {len(successful)}",
        f"Total failed: {len(failed)}",
        f"Success rate: {(len(successful) / len(results) * 100) if results else 0.0:.1f}%",
        "",
        "=== SUCCESSFUL FILES (VERIFIED) ===",
    ]

    for result in successful:
        output_file = Path(result.output).name if result.output else "no output"
        summary_lines.append(f"✓ {result.file} -> {output_file}")

    summary_lines.extend(
        [
            "",
            "=== FAILED FILES (VERIFICATION) ===",
        ]
    )

    summary_lines.extend([f"✗ {result.file}" for result in failed])

    summary_lines.extend(
        [
            "",
            "=== PARALLEL PROCESSING FEATURES ===",
            f"Parallel workers: {config.max_workers}",
            f"API rate limiting: {config.api_rate_limit_delay}s between calls",
            f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}",
        ]
    )

    if config.debug_mode:
        summary_lines.extend(
            [
                "- Saves original specification as *_iter_0_original"
                + config.language_config.file_extension,
                "- Saves initial generated code as *_iter_1_generated"
                + config.language_config.file_extension,
                "- Saves current working version for each iteration as *_iter_N_current"
                + config.language_config.file_extension,
                "- Saves final implementation as *_impl"
                + config.language_config.file_extension,
                "- Full debugging: all intermediate files are saved",
            ]
        )
    else:
        summary_lines.extend(
            [
                "- Saves only final implementation as *_impl"
                + config.language_config.file_extension,
                "- No intermediate files saved (debug mode disabled)",
            ]
        )

    summary_lines.extend(
        [
            "",
            f"- Debug mode control: {'Enabled' if config.debug_mode else 'Disabled'}",
            "- Configurable file output based on debug setting",
            "",
            f"Generated on: {datetime.now().isoformat()}",
        ]
    )

    summary = "\n".join(summary_lines)

    with Path(config.summary_file).open("w") as f:
        f.write(summary)

    return summary
