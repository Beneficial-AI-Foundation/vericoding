#!/usr/bin/env python3
"""
Unified Specification-to-Code Processing

This script processes specification files containing declarations for Dafny, Lean, or Verus,
generates implementations using various LLM APIs, and iteratively fixes verification errors.
"""

import argparse
import math
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime
from pathlib import Path

import wandb

# Import the modular components
from vericoding.core import (
    load_environment,
    ProcessingConfig,
    PromptLoader,
    create_llm_provider,
)
from vericoding.core.language_tools import (
    get_tool_path,
    check_tool_availability,
    find_spec_files,
)
from vericoding.core.llm_providers import get_global_token_stats
from vericoding.processing import process_files_parallel
from vericoding.utils import (
    generate_summary,
    generate_csv_results,
    get_git_remote_url,
    get_current_branch,
)

# Initialize environment loading
load_environment()


def apply_sharding(
    files: list[str], shard_spec: str | None, limit: int | None = None
) -> tuple[list[str], str]:
    """Apply sharding to file list and return selected files with description."""
    total = len(files)

    if shard_spec:
        # Parse shard spec like "2/5"
        try:
            current, total_shards = map(int, shard_spec.split("/"))
        except ValueError:
            raise ValueError(
                f"Invalid shard format: {shard_spec}. Use format K/N (e.g., '2/5')"
            )

        if current < 1 or current > total_shards:
            raise ValueError(
                f"Invalid shard {current}/{total_shards}: shard number must be between 1 and {total_shards}"
            )

        # Calculate this shard's slice
        shard_size = math.ceil(total / total_shards)
        start = (current - 1) * shard_size
        end = min(current * shard_size, total)

        selected = files[start:end]

        description = (
            f"shard {current}/{total_shards} (files {start + 1}-{end} of {total})"
        )
    else:
        # No sharding, just apply limit if specified
        selected = files[:limit] if limit else files
        if limit and limit < total:
            description = f"first {limit} of {total} files"
        else:
            description = f"all {total} files"

    return selected, description


def parse_arguments():
    """Parse command-line arguments."""
    # Get available languages for argument choices
    available_languages = ProcessingConfig.get_available_languages()

    parser = argparse.ArgumentParser(
        description="Unified Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(available_languages.keys())}
Supported LLM providers: claude-sonnet, claude-opus, gpt, gpt-mini, o1, gemini, gemini-flash, grok, grok-code, deepseek, glm, mistral-medium, mistral-codestral, qwen-thinking, qwen-coder, claude-direct, openai-direct, grok-direct, claude, openai

Examples:
  uv run vericoder.py dafny ./specs --llm gemini-flash
  uv run vericoder.py lean ./NumpySpec/DafnySpecs --iterations 3 --llm claude-sonnet
  uv run vericoder.py verus ./benchmarks/verus_specs --iterations 5 --llm gpt
  uv run vericoder.py dafny ./specs --shard 2/5 --llm gemini-flash  # Process shard 2 of 5
  uv run vericoder.py verus ./specs --workers 8 --llm deepseek
        """,
    )

    parser.add_argument(
        "language",
        type=str,
        choices=list(available_languages.keys()),
        help="Programming language to process",
    )

    parser.add_argument("folder", type=Path, help="Directory with specification files")

    parser.add_argument(
        "--iterations",
        "-i",
        type=int,
        default=5,
        help="Max verification attempts per file (default: 5)",
    )

    parser.add_argument(
        "--no-debug",
        action="store_true",
        help="Disable debug mode (debug mode is enabled by default)",
    )

    parser.add_argument(
        "--no-wandb",
        action="store_true",
        help="Disable Weights & Biases experiment tracking",
    )

    parser.add_argument(
        "--delete-after-upload",
        action="store_true",
        help="Delete local generated files after uploading to wandb (requires wandb to be enabled)",
    )

    parser.add_argument(
        "--workers",
        "-w",
        type=int,
        default=4,
        help="Number of parallel workers (default: 4)",
    )

    parser.add_argument(
        "--api-rate-limit-delay",
        type=int,
        default=1,
        help="Delay between API calls in seconds (default: 1)",
    )

    parser.add_argument(
        "--max-directory-traversal-depth",
        type=int,
        default=50,
        help="Maximum depth for directory traversal (default: 50)",
    )

    parser.add_argument(
        "--llm",
        type=str,
        required=True,
        help="LLM to use (provider/model alias, e.g., gemini-flash, claude-sonnet, openai-direct)",
    )
    parser.add_argument(
        "--limit",
        "-n",
        type=int,
        help="Process only the first N files from the dataset (default: process all files)",
    )

    parser.add_argument(
        "--shard",
        type=str,
        help="Process shard K of N total shards (format: K/N, e.g., '2/5' for shard 2 of 5)",
    )

    parser.add_argument(
        "--assume-unformatted-lean",
        action="store_true",
        help="For Lean files, wrap each 'sorry' with vc-theorems tags (only valid for Lean language)",
    )

    parser.add_argument(
        "--tag",
        type=str,
        help="Tag to add to W&B run for experiment tracking",
    )

    return parser.parse_args()


def setup_configuration(args) -> ProcessingConfig:
    """Set up processing configuration from command line arguments."""
    available_languages = ProcessingConfig.get_available_languages()
    language_config = available_languages[args.language]

    # Validate assume-unformatted-lean argument
    if args.assume_unformatted_lean and args.language != "lean":
        print(
            f"Error: --assume-unformatted-lean can only be used with Lean language, not '{args.language}'"
        )
        sys.exit(1)

    print(
        f"=== {language_config.name} Specification-to-Code Processing Configuration ===\n"
    )

    files_dir = str(args.folder)

    if not Path(files_dir).is_dir():
        print(f"Error: Directory '{files_dir}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory outside the input directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")

    # Determine LLM name for output directory (from --llm)
    llm_name = (args.llm or "llm").lower()
    # Sanitize for filesystem paths
    llm_name = llm_name.replace("/", "_").replace(":", "_").replace(" ", "_")

    # Extract the relevant part of the input path for the output hierarchy
    input_path = Path(files_dir).resolve()

    # Find the src directory or use current working directory as base
    current_path = input_path
    src_base = None
    depth = 0
    while (
        current_path.parent != current_path
        and depth < args.max_directory_traversal_depth
    ):
        if current_path.name == "src":
            src_base = current_path
            break
        current_path = current_path.parent
        depth += 1

    if src_base is None:
        # If no 'src' directory found, use the directory containing the input as base
        if input_path.parent.name == "src":
            src_base = input_path.parent
        else:
            # Fallback: find a reasonable base directory
            working_dir = Path.cwd()
            src_base = (
                working_dir / "src" if (working_dir / "src").exists() else working_dir
            )

    # Create output directory alongside the input directory, named: vericoder_<llm>_<date>
    output_dir = str(input_path.parent / f"vericoder_{llm_name}_{timestamp}")
    summary_file = str(Path(output_dir) / "summary.txt")

    Path(output_dir).mkdir(parents=True, exist_ok=True)
    print(f"Created output directory: {output_dir}")

    # Create configuration object
    config = ProcessingConfig(
        language=args.language,
        language_config=language_config,
        files_dir=files_dir,
        max_iterations=args.iterations,
        output_dir=output_dir,
        summary_file=summary_file,
        debug_mode=not args.no_debug,
        max_workers=args.workers,
        api_rate_limit_delay=args.api_rate_limit_delay,
        llm=args.llm,
        max_directory_traversal_depth=args.max_directory_traversal_depth,
        assume_unformatted_lean=args.assume_unformatted_lean,
    )

    print("\nConfiguration:")
    print(f"- Language: {language_config.name}")
    print(f"- Directory: {files_dir}")
    print(f"- Output directory: {output_dir}")
    print(f"- Max iterations: {config.max_iterations}")
    print(f"- Parallel workers: {config.max_workers}")
    print(f"- Tool path: {get_tool_path(config)}")
    print(f"- LLM: {config.llm}")
    print(f"- Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print(f"- API rate limit delay: {config.api_rate_limit_delay}s")
    print("\nProceeding with configuration...")

    return config


def get_tool_version(config: ProcessingConfig) -> str:
    """Get the version of the language tool being used."""
    try:
        tool_path = get_tool_path(config)
        if config.language == "verus":
            result = subprocess.run(
                [tool_path, "--version"], capture_output=True, text=True, timeout=10
            )
        elif config.language == "lean":
            result = subprocess.run(
                [tool_path, "--version"], capture_output=True, text=True, timeout=10
            )
        elif config.language == "dafny":
            result = subprocess.run(
                [tool_path, "/version"], capture_output=True, text=True, timeout=10
            )
        else:
            return f"Unknown tool version for {config.language}"

        if result.returncode == 0:
            return result.stdout.strip()
        else:
            return f"Failed to get version: {result.stderr.strip()}"
    except Exception as e:
        return f"Error getting version: {str(e)}"


def get_experiment_metadata(
    config: ProcessingConfig, args, prompt_loader: PromptLoader = None
) -> dict:
    """Collect comprehensive metadata for the experiment."""
    # Get git information
    git_url = get_git_remote_url()
    git_branch = get_current_branch()

    # Get git commit hash
    git_commit = None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, timeout=5
        )
        if result.returncode == 0:
            git_commit = result.stdout.strip()
    except Exception:
        pass

    # Get hostname
    hostname = platform.node()

    # Get tool version
    tool_version = get_tool_version(config)

    # Determine input type based on directory contents
    input_type = determine_input_type(config.files_dir)

    # Get system prompts if prompt_loader is available
    system_prompts = {}
    if prompt_loader:
        system_prompts = prompt_loader.prompts.copy()

    metadata = {
        # Basic experiment info
        "language": config.language,
        "max_iterations": config.max_iterations,
        "llm": config.llm,
        "max_workers": config.max_workers,
        # File and benchmark info
        "files_dir": config.files_dir,
        "input_type": input_type,
        "benchmark_files_total": len(find_spec_files(config)),
        "shard": args.shard,
        "limit": args.limit,
        # Tool versions and environment
        "tool_version": tool_version,
        "python_version": platform.python_version(),
        "platform": platform.system(),
        "platform_version": platform.release(),
        "hostname": hostname,
        # Git information
        "git_url": git_url,
        "git_branch": git_branch,
        "git_commit": git_commit,
        # Run configuration
        "api_rate_limit_delay": config.api_rate_limit_delay,
        "debug_mode": config.debug_mode,
        "timestamp": datetime.now().isoformat(),
        # Command line arguments (for reproducibility)
        "args": vars(args),
    }

    # Add system prompts if available
    if system_prompts:
        metadata["system_prompts"] = system_prompts

    return metadata


def determine_input_type(files_dir: str) -> str:
    """Determine the input type based on directory contents or name."""
    files_dir_name = Path(files_dir).name.lower()

    if "spec" in files_dir_name:
        return "spec"
    elif "vibe" in files_dir_name:
        return "vibe"
    else:
        # Try to detect from file contents or structure
        spec_keywords = [
            "requires",
            "ensures",
            "invariant",
            "precondition",
            "postcondition",
        ]
        try:
            # Sample a few files to detect type
            # Look for files in the directory to sample
            files_path = Path(files_dir)
            sample_files = []
            if files_path.exists():
                for ext in ["*.dfy", "*.rs", "*.lean"]:
                    sample_files.extend(list(files_path.rglob(ext))[:2])
            if sample_files:
                for file_path in sample_files[:3]:
                    try:
                        with open(file_path, "r") as f:
                            content = f.read().lower()
                            if any(keyword in content for keyword in spec_keywords):
                                return "spec"
                    except Exception:
                        continue
        except Exception:
            pass

        return "both"  # Default fallback


def log_experiment_results_to_wandb(
    config: ProcessingConfig,
    results: list,
    processing_time: float,
    success_percentage: float,
    args,
) -> None:
    """Log comprehensive experiment results to wandb."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success and not r.has_bypass]
    bypassed = [r for r in results if r.has_bypass]
    original_compilation_failed = [
        r for r in results if getattr(r, "original_compilation_failed", False)
    ]

    # Get global token statistics for summary
    token_stats = get_global_token_stats()

    # Log final summary metrics with better organization
    summary_metrics = {
        # Core results
        "results/total_files": len(results),
        "results/successful_files": len(successful),
        "results/failed_files": len(failed),
        "results/bypassed_files": len(bypassed),
        "results/original_compilation_failed_files": len(original_compilation_failed),
        "results/success_rate_percent": success_percentage,
        # Timing information
        "performance/duration_seconds": processing_time,
        "performance/avg_time_per_file": processing_time / len(results)
        if results
        else 0,
        "performance/throughput_files_per_minute": (len(results) / processing_time) * 60
        if processing_time > 0
        else 0,
        # Resource usage
        "resources/parallel_workers": config.max_workers,
        "resources/api_rate_limit_delay": config.api_rate_limit_delay,
        # Token usage summary
        "llm/total_input_tokens": token_stats["input_tokens"],
        "llm/total_output_tokens": token_stats["output_tokens"],
        "llm/total_tokens": token_stats["input_tokens"] + token_stats["output_tokens"],
        "llm/total_calls": token_stats["total_calls"],
        "llm/avg_tokens_per_call": (
            token_stats["input_tokens"] + token_stats["output_tokens"]
        )
        / token_stats["total_calls"]
        if token_stats["total_calls"] > 0
        else 0,
    }

    for key, value in summary_metrics.items():
        wandb.run.summary[key] = value

    # Create comprehensive results table with file contents
    results_table = wandb.Table(
        columns=[
            "file_name",
            "subfolder",
            "success",
            "output_file",
            "error_message",
            "has_bypass",
            "file_path",
            "original_spec",
            "final_output",
            "debug_files",
            "generate_prompt",
            "fix_prompts",
        ]
    )

    for result in results:
        file_path = Path(result.file)
        subfolder = file_path.parts[0] if len(file_path.parts) > 1 else "root"
        output_name = Path(result.output).name if result.output else ""
        error_preview = (
            (result.error[:500] + "...")
            if result.error and len(result.error) > 500
            else (result.error or "")
        )

        # Read original specification file
        original_spec = ""
        try:
            original_file_path = Path(config.files_dir) / result.file
            if original_file_path.exists():
                with open(original_file_path, "r", encoding="utf-8") as f:
                    original_spec = f.read()
        except Exception as e:
            original_spec = f"Error reading original file: {str(e)}"

        # Read final output file
        final_output = ""
        if result.output:
            try:
                with open(result.output, "r", encoding="utf-8") as f:
                    final_output = f.read()
            except Exception as e:
                final_output = f"Error reading output file: {str(e)}"

        # Collect debug files content
        debug_files_content = {}
        if config.debug_mode:
            # Look for debug files for this specific file
            relative_path = Path(result.file)
            debug_dir = (
                Path(config.output_dir) / "debug" / relative_path.parent
                if relative_path.parent != Path(".")
                else Path(config.output_dir) / "debug"
            )

            if debug_dir.exists():
                file_stem = Path(result.file).stem
                for debug_file in debug_dir.glob(f"*{file_stem}*"):
                    try:
                        with open(debug_file, "r", encoding="utf-8") as f:
                            content = f.read()
                            debug_files_content[debug_file.name] = content
                    except Exception as e:
                        debug_files_content[debug_file.name] = (
                            f"Error reading: {str(e)}"
                        )

        # Format debug files as readable text
        debug_files_text = ""
        if debug_files_content:
            debug_files_text = "\\n\\n".join(
                [
                    f"=== {filename} ===\\n{content}"
                    for filename, content in debug_files_content.items()
                ]
            )

        results_table.add_data(
            file_path.name,
            subfolder,
            result.success,
            output_name,
            error_preview,
            result.has_bypass,
            str(result.file),
            original_spec,
            final_output,
            debug_files_text or "No debug files",
            result.generate_prompt
            if hasattr(result, "generate_prompt") and result.generate_prompt
            else "",
            "\\n\\n---\\n\\n".join(result.fix_prompts)
            if hasattr(result, "fix_prompts") and result.fix_prompts
            else "",
        )

    wandb.log({"detailed_results": results_table})

    # Upload comprehensive artifacts with better organization
    print("\\n📤 Uploading experiment artifacts to wandb...")

    # Create unique artifact names using run timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # 1. Generated code artifact
    code_artifact = wandb.Artifact(
        name=f"generated_code_{config.language}_{timestamp}",
        type="generated-code",
        description=f"Generated {config.language} code from specifications",
        metadata={
            "language": config.language,
            "success_rate": success_percentage,
            "total_files": len(results),
            "llm_model": config.llm,
            "timestamp": timestamp,
        },
    )

    # 2. Debug files artifact (if debug mode enabled)
    debug_artifact = None
    if config.debug_mode:
        debug_artifact = wandb.Artifact(
            name=f"debug_files_{config.language}_{timestamp}",
            type="debug-files",
            description=f"Debug and intermediate files from {config.language} processing",
            metadata={
                "language": config.language,
                "debug_mode": True,
                "iterations": config.max_iterations,
                "timestamp": timestamp,
            },
        )

    # 3. Summary and analysis artifact
    summary_artifact = wandb.Artifact(
        name=f"analysis_{config.language}_{timestamp}",
        type="analysis",
        description=f"Summary reports and CSV analysis for {config.language} experiment",
        metadata={
            "language": config.language,
            "total_files": len(results),
            "success_rate": success_percentage,
            "timestamp": timestamp,
        },
    )

    # Add files to artifacts
    output_path = Path(config.output_dir)
    if output_path.exists():
        for file_path in output_path.rglob("*"):
            if file_path.is_file():
                relative_path = file_path.relative_to(output_path)

                # Categorize files into appropriate artifacts
                if file_path.suffix in [".dfy", ".rs", ".lean"] and not any(
                    keyword in file_path.name for keyword in ["iter_", "debug"]
                ):
                    # Final implementation files go to code artifact
                    code_artifact.add_file(str(file_path), name=str(relative_path))
                elif config.debug_mode and (
                    "debug" in str(relative_path)
                    or "iter_" in file_path.name
                    or "error.log" in file_path.name
                ):
                    # Debug/intermediate files and error logs go to debug artifact
                    if debug_artifact:
                        debug_artifact.add_file(str(file_path), name=str(relative_path))
                elif file_path.suffix in [".txt", ".csv"]:
                    # Summary and analysis files go to analysis artifact
                    summary_artifact.add_file(str(file_path), name=str(relative_path))
                else:
                    # Fallback to code artifact for other files
                    code_artifact.add_file(str(file_path), name=str(relative_path))

    # Log all artifacts
    wandb.log_artifact(code_artifact)
    print(
        f"✅ Generated code uploaded to wandb artifact: generated_code_{config.language}_{timestamp}"
    )

    if debug_artifact and config.debug_mode:
        wandb.log_artifact(debug_artifact)
        print(
            f"✅ Debug files uploaded to wandb artifact: debug_files_{config.language}_{timestamp}"
        )

    wandb.log_artifact(summary_artifact)
    print(
        f"✅ Analysis files uploaded to wandb artifact: analysis_{config.language}_{timestamp}"
    )

    # Store key files directly in wandb.summary for easy access
    if output_path.exists():
        summary_file = output_path / "summary.txt"
        if summary_file.exists():
            try:
                with open(summary_file, "r") as f:
                    wandb.run.summary["experiment_summary"] = f.read()
            except Exception as e:
                print(f"Warning: Could not read summary file: {e}")

        csv_file = output_path / "results.csv"
        if csv_file.exists():
            wandb.run.summary["results_csv_path"] = str(csv_file)

    # Delete local files if requested
    if args.delete_after_upload:
        try:
            shutil.rmtree(output_path)
            print(f"🗑️ Local files deleted from {output_path}")
        except Exception as e:
            print(f"⚠️ Error deleting local files: {e}")

    # Finish wandb run
    wandb.finish()


def main():
    """Main entry point for the specification-to-code processing."""
    # Parse command-line arguments first
    args = parse_arguments()

    if args.limit and args.shard:
        raise ValueError("Cannot specify limit and shard")

    # Set up configuration
    config = setup_configuration(args)

    # Initialize wandb for experiment tracking (unless disabled)
    wandb_run = None
    if not args.no_wandb and os.getenv("WANDB_API_KEY"):
        try:
            # Include shard in run name if specified
            shard_suffix = ""
            if args.shard:
                shard_suffix = f"_shard{args.shard.replace('/', 'of')}"

            # Initialize wandb run
            run_name = f"vericoding_{config.language}_{datetime.now().strftime('%Y%m%d_%H%M%S')}{shard_suffix}"

            # Get comprehensive metadata
            experiment_metadata = get_experiment_metadata(config, args)

            # Build tags list
            tags = [config.language, config.llm, "spec-to-code"]
            if args.tag:
                tags.append(args.tag)

            wandb_run = wandb.init(
                project=os.getenv("WANDB_PROJECT", "vericoding"),
                entity=os.getenv("WANDB_ENTITY"),
                name=run_name,
                tags=tags,
                mode=os.getenv("WANDB_MODE", "online"),
            )
            # Update config with comprehensive metadata
            wandb.config.update(experiment_metadata, allow_val_change=True)
            print(f"✅ Weights & Biases tracking enabled: {run_name}")
            if wandb_run:
                print(f"   View at: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Failed to initialize wandb: {e}")
            wandb_run = None
            # Ensure wandb.run is cleared when initialization fails
            try:
                wandb.finish()
            except Exception:
                pass
    else:
        if args.no_wandb:
            print("⚠️  Weights & Biases tracking disabled (--no-wandb flag)")
        else:
            print("⚠️  Weights & Biases tracking disabled (WANDB_API_KEY not set)")

    # Initialize prompt loader for the selected language
    try:
        prompt_loader = PromptLoader(
            config.language, prompts_file=config.language_config.prompts_file
        )
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation.valid:
            print(f"Warning: Missing required prompts: {', '.join(validation.missing)}")
            print(f"Available prompts: {', '.join(validation.available)}")
            sys.exit(1)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print(
            f"Please ensure the {config.language_config.prompts_file} file exists in the {config.language} directory."
        )
        print("Expected locations:")
        script_dir = Path(__file__).parent
        print(
            f"  - {script_dir / config.language / config.language_config.prompts_file}"
        )
        print(f"  - {config.language_config.prompts_file} (current directory)")
        sys.exit(1)

    # Log system prompts to wandb if enabled
    if wandb_run:
        try:
            # Get updated metadata with prompts
            experiment_metadata_with_prompts = get_experiment_metadata(
                config, args, prompt_loader
            )

            # Log system prompts specifically
            if "system_prompts" in experiment_metadata_with_prompts:
                wandb.config.update(
                    {
                        "system_prompts": experiment_metadata_with_prompts[
                            "system_prompts"
                        ]
                    },
                    allow_val_change=True,
                )
                print("✅ System prompts logged to wandb")

                # Also log prompts as a text artifact for easier viewing
                prompts_artifact = wandb.Artifact(
                    name=f"system_prompts_{config.language}_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                    type="prompts",
                    description=f"System prompts for {config.language} code generation",
                    metadata={
                        "language": config.language,
                        "prompts_file": config.language_config.prompts_file,
                        "num_prompts": len(
                            experiment_metadata_with_prompts["system_prompts"]
                        ),
                    },
                )

                # Create a formatted text file with the prompts
                with tempfile.NamedTemporaryFile(
                    mode="w", suffix=".txt", delete=False
                ) as tmp_file:
                    tmp_file.write(f"System Prompts for {config.language}\n")
                    tmp_file.write("=" * 80 + "\n\n")

                    for prompt_name, prompt_content in experiment_metadata_with_prompts[
                        "system_prompts"
                    ].items():
                        tmp_file.write(f"Prompt: {prompt_name}\n")
                        tmp_file.write("-" * 40 + "\n")
                        tmp_file.write(prompt_content)
                        tmp_file.write("\n\n" + "=" * 80 + "\n\n")

                    tmp_path = tmp_file.name

                # Add the file to the artifact
                prompts_artifact.add_file(tmp_path, name="system_prompts.txt")
                wandb.log_artifact(prompts_artifact)

                # Clean up temp file
                os.unlink(tmp_path)

                print("✅ System prompts artifact uploaded to wandb")
        except Exception as e:
            print(f"⚠️  Failed to log system prompts to wandb: {e}")

    print(
        f"Starting specification-to-code processing of {config.language_config.name} files (PARALLEL VERSION)..."
    )
    print(f"Directory: {config.files_dir}")
    print(f"Output directory: {config.output_dir}")
    print(f"Tool path: {get_tool_path(config)}")
    print(f"Max iterations: {config.max_iterations}")
    print(f"Parallel workers: {config.max_workers}")
    print(f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print("Processing each file by generating code from specifications.")
    if config.debug_mode:
        print(
            "DEBUG MODE: Saves code after each iteration to debug/ subdirectory for analysis."
        )
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    # Check if the required API key is available for the selected LLM provider
    try:
        # This will raise an error if the API key is not available
        llm_provider, resolved_model = create_llm_provider(config.llm)
        # Note: The create_llm_provider function already prints the success message
    except Exception as e:
        print(f"Error: {str(e)}")
        print("")
        print(
            "Note: .env files are automatically loaded if they exist in the current or parent directory."
        )
        sys.exit(1)

    print("")
    print(f"Checking {config.language_config.name} availability...")
    tool_availability = check_tool_availability(config)
    if not tool_availability.available:
        print(f"Error: {tool_availability.message}")
        print(
            f"Please ensure {config.language_config.name} is installed and the {config.language_config.tool_path_env} environment variable is set correctly."
        )
        print(
            f"Current {config.language_config.tool_path_env}: {get_tool_path(config)}"
        )
        print(
            f"You can set it with: export {config.language_config.tool_path_env}=/path/to/{config.language}"
        )
        sys.exit(1)

    print(f"✓ {tool_availability.message}")
    print("")

    # Find all specification files (already sorted)
    all_spec_files = find_spec_files(config)

    # Apply sharding/limiting
    try:
        spec_files, selection_desc = apply_sharding(
            all_spec_files, args.shard, args.limit
        )
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)

    print(
        f"Found {len(all_spec_files)} {config.language_config.name} specification files"
    )
    print(f"Processing: {selection_desc}")
    if config.language == "lean":
        print("(Only Lean files containing 'sorry' are selected)")
    print("")

    if not spec_files:
        print(f"No {config.language_config.name} files found. Exiting.")
        return

    # Process files in parallel
    start_time = time.time()
    results = process_files_parallel(config, prompt_loader, spec_files)
    end_time = time.time()
    processing_time = end_time - start_time

    # Generate summary
    print("")
    print("Generating summary...")
    summary = generate_summary(config, results)

    print("")
    print("=== SUMMARY ===")
    print(summary)
    print("")
    print(f"Summary saved to: {config.summary_file}")
    print(f"All generated files saved to: {config.output_dir}")
    print(f"Total processing time: {processing_time:.2f} seconds")
    print(f"Average time per file: {processing_time / len(results):.2f} seconds")
    if config.debug_mode:
        print(
            "DEBUG: Debug files saved in debug/ subdirectory (original, generated, current per iteration), final implementation in main output directory"
        )
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    generate_csv_results(config, results)

    # Subfolder analysis removed

    # Print final statistics
    successful = [r for r in results if r.success]
    success_percentage = len(successful) / len(results) * 100 if results else 0

    print(
        f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({success_percentage:.1f}%)"
    )
    print(
        f"⚡ Parallel processing with {config.max_workers} workers completed in {processing_time:.2f}s"
    )

    # Print token usage summary
    token_stats = get_global_token_stats()
    print(
        f"📊 Token Usage: {token_stats['input_tokens']:,} input + {token_stats['output_tokens']:,} output = {token_stats['input_tokens'] + token_stats['output_tokens']:,} total tokens ({token_stats['total_calls']} calls)"
    )

    # Log comprehensive experiment summary to wandb (if enabled)
    if wandb_run:
        try:
            log_experiment_results_to_wandb(
                config, results, processing_time, success_percentage, args
            )
            print(f"\n✅ Wandb run completed: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Error logging to wandb: {e}")


if __name__ == "__main__":
    main()
