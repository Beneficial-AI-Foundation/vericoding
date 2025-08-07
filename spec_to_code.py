#!/usr/bin/env python3
"""
Unified Specification-to-Code Processing

This script processes specification files containing declarations for Dafny, Lean, or Verus,
generates implementations using various LLM APIs, and iteratively fixes verification errors.
"""

import argparse
import os
import shutil
import sys
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
from vericoding.processing import process_files_parallel
from vericoding.utils import generate_summary, generate_csv_results

# Initialize environment loading
load_environment()


def parse_arguments():
    """Parse command-line arguments."""
    # Get available languages for argument choices
    available_languages = ProcessingConfig.get_available_languages()

    parser = argparse.ArgumentParser(
        description="Unified Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(available_languages.keys())}
Supported LLM providers: claude, openai, deepseek

Examples:
  python spec_to_code.py dafny ./specs
  python spec_to_code.py lean ./NumpySpec/DafnySpecs --iterations 3
  python spec_to_code.py verus ./benchmarks/verus_specs --debug --iterations 5
  python spec_to_code.py dafny ./specs --workers 8 --iterations 3 --llm-provider openai
  python spec_to_code.py verus ./specs --workers 2 --debug --llm-provider deepseek --llm-model deepseek-chat
  python spec_to_code.py dafny ./specs --llm-provider claude --llm-model claude-3-5-sonnet-20241022
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
        "--debug",
        action="store_true",
        help="Enable debug mode (save intermediate files)",
    )

    parser.add_argument(
        "--strict-specs",
        action="store_true",
        help="Enable strict specification preservation (default: relaxed verification)",
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
        "--llm-provider",
        type=str,
        choices=["claude", "openai", "deepseek"],
        default="claude",
        help="LLM provider to use (default: claude)",
    )

    parser.add_argument(
        "--llm-model",
        type=str,
        help="Specific model to use (defaults to provider's default model)",
    )

    return parser.parse_args()


def setup_configuration(args) -> ProcessingConfig:
    """Set up processing configuration from command line arguments."""
    available_languages = ProcessingConfig.get_available_languages()
    language_config = available_languages[args.language]

    print(
        f"=== {language_config.name} Specification-to-Code Processing Configuration ===\n"
    )

    files_dir = str(args.folder)

    if not Path(files_dir).is_dir():
        print(f"Error: Directory '{files_dir}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory outside the input directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")

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

    # Calculate the relative path from src_base to the input directory
    try:
        relative_from_src = input_path.relative_to(src_base)
        path_parts = relative_from_src.parts

        # Try to find a meaningful subset
        meaningful_part = None
        for _i, part in enumerate(path_parts):
            if part in [
                "autoverus",
                "clover",
                "synthesis_task",
                "first_8",
                "atomizer_supported",
                "atomizer_supported_tasks_dep_only",
                "numpy_specs",
                "DafnySpecs",
                "benchmarks",
            ]:
                meaningful_part = Path(part)
                break

        if meaningful_part is None:
            # If no recognized pattern, use the last 1-2 directory levels
            if len(path_parts) >= 2:
                meaningful_part = Path(path_parts[-2]) / Path(path_parts[-1])
            else:
                meaningful_part = Path(path_parts[-1]) if path_parts else Path("specs")

    except ValueError:
        # input_path is not relative to src_base, use the basename
        meaningful_part = Path(input_path.name)

    # Create output directory structure
    output_dir = str(
        src_base / f"code_from_spec_on_{timestamp}" / args.language / meaningful_part
    )
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
        debug_mode=args.debug,
        strict_spec_verification=args.strict_specs,
        max_workers=args.workers,
        api_rate_limit_delay=args.api_rate_limit_delay,
        llm_provider=args.llm_provider,
        llm_model=args.llm_model,
        max_directory_traversal_depth=args.max_directory_traversal_depth,
    )

    print("\nConfiguration:")
    print(f"- Language: {language_config.name}")
    print(f"- Directory: {files_dir}")
    print(f"- Output directory: {output_dir}")
    print(f"- Max iterations: {config.max_iterations}")
    print(f"- Parallel workers: {config.max_workers}")
    print(f"- Tool path: {get_tool_path(config)}")
    print(f"- LLM Provider: {config.llm_provider}")
    print(f"- LLM Model: {config.llm_model or 'default'}")
    print(f"- Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print(
        f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}"
    )
    print(f"- API rate limit delay: {config.api_rate_limit_delay}s")
    print("\nProceeding with configuration...")

    return config


def main():
    """Main entry point for the specification-to-code processing."""
    # Parse command-line arguments first
    args = parse_arguments()

    # Set up configuration
    config = setup_configuration(args)
    
    # Initialize wandb for experiment tracking (unless disabled)
    wandb_run = None
    if not args.no_wandb and os.getenv("WANDB_API_KEY"):
        try:
            # Initialize wandb run
            run_name = f"vericoding_{config.language}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            wandb_config = {
                "language": config.language,
                "max_iterations": config.max_iterations,
                "llm_provider": config.llm_provider,
                "llm_model": config.llm_model,
                "strict_spec_verification": config.strict_spec_verification,
                "max_workers": config.max_workers,
                "files_dir": config.files_dir,
            }
            
            wandb_run = wandb.init(
                project=os.getenv("WANDB_PROJECT", "vericoding"),
                entity=os.getenv("WANDB_ENTITY"),
                name=run_name,
                tags=[config.language, config.llm_provider],
                mode=os.getenv("WANDB_MODE", "online")
            )
            # Update config with allow_val_change to avoid errors when keys already exist
            wandb.config.update(wandb_config, allow_val_change=True)
            print(f"✅ Weights & Biases tracking enabled: {run_name}")
            if wandb_run:
                print(f"   View at: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Failed to initialize wandb: {e}")
            wandb_run = None
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

    print(
        f"Starting specification-to-code processing of {config.language_config.name} files (PARALLEL VERSION)..."
    )
    print(f"Directory: {config.files_dir}")
    print(f"Output directory: {config.output_dir}")
    print(f"Tool path: {get_tool_path(config)}")
    print(f"Max iterations: {config.max_iterations}")
    print(f"Parallel workers: {config.max_workers}")
    print(f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print(
        f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}"
    )
    print("Processing each file by generating code from specifications.")
    if config.debug_mode:
        print(
            "DEBUG MODE: Saves code after each iteration to separate files for analysis."
        )
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    # Check if the required API key is available for the selected LLM provider
    try:
        # This will raise an error if the API key is not available
        create_llm_provider(config.llm_provider, config.llm_model)
        print(f"✓ {config.llm_provider.upper()} API key found and provider initialized")
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

    # Find all specification files
    spec_files = find_spec_files(config)
    print(f"Found {len(spec_files)} {config.language_config.name} files to process")
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
            "DEBUG: Files saved: original, generated, current per iteration, and final implementation"
        )
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    generate_csv_results(config, results)

    # Print final statistics
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success and not r.has_bypass]
    bypassed = [r for r in results if r.has_bypass]
    
    print(
        f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({len(successful) / len(results) * 100:.1f}%)"
    )
    print(
        f"⚡ Parallel processing with {config.max_workers} workers completed in {processing_time:.2f}s"
    )
    
    # Log experiment summary to wandb (if enabled)
    if wandb_run:
        try:
            # Log final summary metrics
            wandb.run.summary["total_files"] = len(results)
            wandb.run.summary["successful_files"] = len(successful)
            wandb.run.summary["failed_files"] = len(failed)
            wandb.run.summary["bypassed_files"] = len(bypassed)
            wandb.run.summary["success_rate"] = len(successful) / len(results) if results else 0
            wandb.run.summary["duration_seconds"] = processing_time
            
            # Upload generated files as artifacts
            print("\n📤 Uploading generated files to wandb...")
            artifact = wandb.Artifact(
                name=f"generated_code_{config.language}",
                type="code",
                description=f"Generated {config.language} code from specifications"
            )
            
            # Add the output directory to the artifact
            output_path = Path(config.output_dir)
            if output_path.exists():
                artifact.add_dir(str(output_path))
                wandb.log_artifact(artifact)
                print(f"✅ Files uploaded to wandb artifact: generated_code_{config.language}")
                
                # Delete local files if requested
                if args.delete_after_upload:
                    try:
                        shutil.rmtree(output_path)
                        print(f"🗑️  Local files deleted from {output_path}")
                    except Exception as e:
                        print(f"⚠️  Error deleting local files: {e}")
            else:
                print(f"⚠️  Output directory not found: {output_path}")
            
            # Finish wandb run
            wandb.finish()
            print(f"\n✅ Wandb run completed: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Error logging to wandb: {e}")


if __name__ == "__main__":
    main()
