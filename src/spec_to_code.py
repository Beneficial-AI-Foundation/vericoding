#!/usr/bin/env python3
"""
Unified Specification-to-Code Processing

This script processes specification files containing declarations for Dafny, Lean, or Verus,
generates implementations using various LLM APIs, and iteratively fixes verification errors.
"""

import argparse
import json
import os
import platform
import shutil
import subprocess
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
from vericoding.utils import (
    generate_summary,
    generate_csv_results,
    generate_subfolder_analysis_csv,
    get_git_remote_url,
    get_current_branch,
)
from vericoding.core import ProcessingConfig
from vericoding.lean.mcp_helpers import ensure_server_started, close_server
import atexit

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
  python spec_to_code.py lean ./benchmarks/lean/dafnybench --iterations 3
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
        default="openai",
        help="LLM provider to use (default: openai).",
    )

    parser.add_argument(
        "--llm-model",
        type=str,
        default="gpt-5",
        help="Specific model to use (default: gpt-5 for OpenAI)",
    )

    parser.add_argument(
        "--reasoning-effort",
        type=str,
        choices=["low", "medium", "high"],
        default="high",
        help="For reasoning-capable models (e.g., gpt-5, o4), set reasoning effort (default: high).",
    )

    parser.add_argument(
        "--lake-build-target",
        type=str,
        help="Optional Lake target to build at the end for overall stats (e.g., DafnyBench)",
    )

    parser.add_argument(
        "--use-mcp",
        action="store_true",
        default=True,
        help="Use Lean LSP MCP to gather hover/goals/diagnostics context and include in prompts (Lean only) [default: enabled]",
    )

    parser.add_argument(
        "--tool-calling",
        action="store_true",
        default=True,
        help="Enable LLM tool-calling (OpenAI) to invoke Lean MCP tools mid-turn [default: enabled]",
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
    # For Lean, place generated files under a sibling namespace so default targets don't pull them in.
    # We use benchmarks/lean/dafnybench_gen/Run_<ts>/... and add a dedicated Lake target.
    if args.language == "lean":
        try:
            from vericoding.utils import get_repo_root  # type: ignore
        except Exception:
            get_repo_root = lambda: Path.cwd()
        repo_root = Path(get_repo_root())
        output_dir = str(repo_root / "benchmarks/lean/dafnybench_gen" / f"Run_{timestamp}")
    else:
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
        llm_reasoning_effort=args.reasoning_effort,
        use_mcp=args.use_mcp,
        llm_tool_calling=args.tool_calling,
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
    if args.reasoning_effort:
        print(f"- Reasoning effort: {args.reasoning_effort}")
    print(f"- Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print(
        f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}"
    )
    print(f"- API rate limit delay: {config.api_rate_limit_delay}s")
    if config.language == 'lean' and config.use_mcp:
        # Attempt to start persistent MCP session (non-fatal)
        ensure_server_started()
        print("- MCP (lean-lsp-mcp): Persistent session enabled")
        atexit.register(close_server)
    print("\nProceeding with configuration...")

    return config


def get_tool_version(config: ProcessingConfig) -> str:
    """Get the version of the language tool being used."""
    try:
        tool_path = get_tool_path(config)
        if config.language == "verus":
            result = subprocess.run([tool_path, "--version"], capture_output=True, text=True, timeout=10)
        elif config.language == "lean":
            result = subprocess.run([tool_path, "--version"], capture_output=True, text=True, timeout=10)
        elif config.language == "dafny":
            result = subprocess.run([tool_path, "/version"], capture_output=True, text=True, timeout=10)
        else:
            return f"Unknown tool version for {config.language}"
        
        if result.returncode == 0:
            return result.stdout.strip()
        else:
            return f"Failed to get version: {result.stderr.strip()}"
    except Exception as e:
        return f"Error getting version: {str(e)}"


def get_experiment_metadata(config: ProcessingConfig, args) -> dict:
    """Collect comprehensive metadata for the experiment."""
    # Get git information
    git_url = get_git_remote_url()
    git_branch = get_current_branch()
    
    # Get git commit hash
    git_commit = None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"], 
            capture_output=True, text=True, timeout=5
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
    
    return {
        # Basic experiment info
        "language": config.language,
        "max_iterations": config.max_iterations,
        "llm_provider": config.llm_provider,
        "llm_model": config.llm_model or f"{config.llm_provider}-default",
        "strict_spec_verification": config.strict_spec_verification,
        "max_workers": config.max_workers,
        
        # File and benchmark info  
        "files_dir": config.files_dir,
        "input_type": input_type,
        "benchmark_files": len(find_spec_files(config)),
        
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


def determine_input_type(files_dir: str) -> str:
    """Determine the input type based on directory contents or name."""
    files_dir_name = Path(files_dir).name.lower()
    
    if "spec" in files_dir_name:
        return "spec"
    elif "vibe" in files_dir_name:
        return "vibe"
    else:
        # Try to detect from file contents or structure
        spec_keywords = ["requires", "ensures", "invariant", "precondition", "postcondition"]
        try:
            # Sample a few files to detect type
            # Look for files in the directory to sample\n            files_path = Path(files_dir)\n            sample_files = []\n            if files_path.exists():\n                for ext in [\"*.dfy\", \"*.rs\", \"*.lean\"]:\n                    sample_files.extend(list(files_path.rglob(ext))[:2])
            if spec_files:
                sample_file = spec_files[0] if len(spec_files) == 1 else spec_files[:min(3, len(spec_files))]
                for file_path in (sample_file if isinstance(sample_file, list) else [sample_file]):
                    try:
                        with open(file_path, 'r') as f:
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
    args
) -> None:
    """Log comprehensive experiment results to wandb."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success and not r.has_bypass]
    bypassed = [r for r in results if r.has_bypass]
    
    # Log final summary metrics with better organization
    summary_metrics = {
        # Core results
        "results/total_files": len(results),
        "results/successful_files": len(successful), 
        "results/failed_files": len(failed),
        "results/bypassed_files": len(bypassed),
        "results/success_rate_percent": success_percentage,
        
        # Timing information
        "performance/duration_seconds": processing_time,
        "performance/avg_time_per_file": processing_time / len(results) if results else 0,
        "performance/throughput_files_per_minute": (len(results) / processing_time) * 60 if processing_time > 0 else 0,
        
        # Resource usage
        "resources/parallel_workers": config.max_workers,
        "resources/api_rate_limit_delay": config.api_rate_limit_delay,
    }
    
    for key, value in summary_metrics.items():
        wandb.run.summary[key] = value
    
    # Create comprehensive results table with file contents
    results_table = wandb.Table(columns=[
        "file_name", "subfolder", "success", "output_file", "error_message",
        "has_bypass", "file_path", "original_spec", "final_output", "debug_files",
        "generate_prompt", "fix_prompts"
    ])
    
    for result in results:
        file_path = Path(result.file)
        subfolder = file_path.parts[0] if len(file_path.parts) > 1 else "root"
        output_name = Path(result.output).name if result.output else ""
        error_preview = (result.error[:500] + "...") if result.error and len(result.error) > 500 else (result.error or "")
        
        # Read original specification file
        original_spec = ""
        try:
            original_file_path = Path(config.files_dir) / result.file
            if original_file_path.exists():
                with open(original_file_path, 'r', encoding='utf-8') as f:
                    original_spec = f.read()
        except Exception as e:
            original_spec = f"Error reading original file: {str(e)}"
        
        # Read final output file
        final_output = ""
        if result.output:
            try:
                with open(result.output, 'r', encoding='utf-8') as f:
                    final_output = f.read()
            except Exception as e:
                final_output = f"Error reading output file: {str(e)}"
        
        # Collect debug files content
        debug_files_content = {}
        if config.debug_mode:
            # Look for debug files for this specific file
            relative_path = Path(result.file)
            debug_dir = Path(config.output_dir) / "debug" / relative_path.parent if relative_path.parent != Path(".") else Path(config.output_dir) / "debug"
            
            if debug_dir.exists():
                file_stem = Path(result.file).stem
                for debug_file in debug_dir.glob(f"*{file_stem}*"):
                    try:
                        with open(debug_file, 'r', encoding='utf-8') as f:
                            content = f.read()
                            debug_files_content[debug_file.name] = content
                    except Exception as e:
                        debug_files_content[debug_file.name] = f"Error reading: {str(e)}"
        
        # Format debug files as readable text
        debug_files_text = ""
        if debug_files_content:
            debug_files_text = "\\n\\n".join([
                f"=== {filename} ===\\n{content}" 
                for filename, content in debug_files_content.items()
            ])
        
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
            result.generate_prompt if hasattr(result, 'generate_prompt') and result.generate_prompt else "",
            "\\n\\n---\\n\\n".join(result.fix_prompts) if hasattr(result, 'fix_prompts') and result.fix_prompts else ""
        )
    
    wandb.log({"detailed_results": results_table})
    
    # Upload comprehensive artifacts with better organization
    print("\\n📤 Uploading experiment artifacts to wandb...")
    
    # Create unique artifact names using run timestamp
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    
    # 1. Generated code artifact
    code_artifact = wandb.Artifact(
        name=f"generated_code_{config.language}_{timestamp}",
        type="generated-code",
        description=f"Generated {config.language} code from specifications",
        metadata={
            "language": config.language,
            "success_rate": success_percentage,
            "total_files": len(results),
            "llm_model": config.llm_model or f"{config.llm_provider}-default",
            "timestamp": timestamp,
        }
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
            }
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
        }
    )
    
    # Add files to artifacts
    output_path = Path(config.output_dir)
    if output_path.exists():
        for file_path in output_path.rglob("*"):
            if file_path.is_file():
                relative_path = file_path.relative_to(output_path)
                
                # Categorize files into appropriate artifacts
                if file_path.suffix in ['.dfy', '.rs', '.lean'] and not any(keyword in file_path.name for keyword in ['iter_', 'debug']):
                    # Final implementation files go to code artifact
                    code_artifact.add_file(str(file_path), name=str(relative_path))
                elif config.debug_mode and ('debug' in str(relative_path) or 'iter_' in file_path.name or 'error.log' in file_path.name):
                    # Debug/intermediate files and error logs go to debug artifact
                    if debug_artifact:
                        debug_artifact.add_file(str(file_path), name=str(relative_path))
                elif file_path.suffix in ['.txt', '.csv']:
                    # Summary and analysis files go to analysis artifact
                    summary_artifact.add_file(str(file_path), name=str(relative_path))
                else:
                    # Fallback to code artifact for other files
                    code_artifact.add_file(str(file_path), name=str(relative_path))
    
    # Log all artifacts
    wandb.log_artifact(code_artifact)
    print(f"✅ Generated code uploaded to wandb artifact: generated_code_{config.language}_{timestamp}")
    
    if debug_artifact and config.debug_mode:
        wandb.log_artifact(debug_artifact)
        print(f"✅ Debug files uploaded to wandb artifact: debug_files_{config.language}_{timestamp}")
    
    wandb.log_artifact(summary_artifact) 
    print(f"✅ Analysis files uploaded to wandb artifact: analysis_{config.language}_{timestamp}")
    
    # Store key files directly in wandb.summary for easy access
    if output_path.exists():
        summary_file = output_path / "summary.txt"
        if summary_file.exists():
            try:
                with open(summary_file, 'r') as f:
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

    # Set up configuration
    config = setup_configuration(args)
    
    # Initialize wandb for experiment tracking (unless disabled)
    wandb_run = None
    if not args.no_wandb and os.getenv("WANDB_API_KEY"):
        try:
            # Initialize wandb run
            run_name = f"vericoding_{config.language}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            # Get comprehensive metadata
            experiment_metadata = get_experiment_metadata(config, args)
            
            wandb_run = wandb.init(
                project=os.getenv("WANDB_PROJECT", "vericoding"),
                entity=os.getenv("WANDB_ENTITY"),
                name=run_name,
                tags=[config.language, config.llm_provider, "spec-to-code"],
                mode=os.getenv("WANDB_MODE", "online")
            )
            # Update config with comprehensive metadata
            wandb.config.update(experiment_metadata, allow_val_change=True)
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
            "DEBUG MODE: Saves code after each iteration to debug/ subdirectory for analysis."
        )
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    # Check if the required API key is available for the selected LLM provider
    try:
        # This will raise an error if the API key is not available
        create_llm_provider(
            config.llm_provider,
            config.llm_model,
            reasoning_effort=getattr(config, "llm_reasoning_effort", None),
        )
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
            "DEBUG: Debug files saved in debug/ subdirectory (original, generated, current per iteration), final implementation in main output directory"
        )
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    generate_csv_results(config, results)

    # Generate subfolder analysis CSV
    generate_subfolder_analysis_csv(config, results)

    # Print final statistics
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success and not r.has_bypass]
    bypassed = [r for r in results if r.has_bypass]
    success_percentage = len(successful) / len(results) * 100 if results else 0
    
    print(
        f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({success_percentage:.1f}%)"
    )
    print(
        f"⚡ Parallel processing with {config.max_workers} workers completed in {processing_time:.2f}s"
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

    # Optionally build a Lake target for coarse-grained stats
    if args.lake_build_target and config.language == "lean":
        print(f"\nBuilding Lake target '{args.lake_build_target}' for summary stats...")
        try:
            proc = subprocess.run(
                ["lake", "build", args.lake_build_target],
                capture_output=True,
                text=True,
                timeout=900,
            )
            combined = proc.stdout + proc.stderr
            sorry_count = combined.count("declaration uses 'sorry'")
            error_count = combined.count("error:")
            print("=== LAKE BUILD SUMMARY ===")
            print(f"Exit code: {proc.returncode}")
            print(f"Errors: {error_count}")
            print(f"'sorry' warnings: {sorry_count}")
            # Save to file alongside summary
            lake_summary_path = Path(config.output_dir) / "lake_build_summary.txt"
            with lake_summary_path.open("w") as f:
                f.write(combined)
            print(f"Full Lake output saved to: {lake_summary_path}")
        except subprocess.TimeoutExpired:
            print("⏱️  Lake build timed out")


if __name__ == "__main__":
    main()
