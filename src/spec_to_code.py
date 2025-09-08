import argparse
import json
import os
import platform
import shutil
import subprocess

import logging
import sys
import time
from pathlib import Path
from vericoding.core.prompts import init_prompt_loader
from vericoding.utils.wandb_utils import init_wandb_run, finalize_wandb_run
from vericoding.utils.io_utils import parse_command_line_arguments, print_startup_info
    
# Import the modular components
from vericoding.core.language_tools import (
    get_tool_path,
    check_tool_availability,
    find_spec_files,
)

 # Initialize environment loading
from vericoding.core.config import load_environment, setup_configuration, ProcessingConfig
from vericoding.core.llm_providers import create_llm_provider
from vericoding.core.language_tools import check_tool_availability,find_spec_files

from vericoding.processing.spec_processor import process_files_parallel
from vericoding.utils.reporting import print_summary

# Initialize environment and logging
load_environment()
logging.basicConfig(level=logging.INFO, format="%(message)s")




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

    # Parse command line arguments
    args = parse_command_line_arguments()

    config = setup_configuration(args)
    llm_provider, resolved_model = create_llm_provider(config.llm)
    
    print_startup_info(config, resolved_model)
    
    # Continue with the rest of initialization
    wandb_run = init_wandb_run(config, args, args.no_wandb, resolved_model)
    # Use mode-based prompt file selection unless a non-default prompts_file is specified
    prompts_file = None if config.language_config.prompts_file == "prompts.yaml" else config.language_config.prompts_file
    prompt_loader = init_prompt_loader(config.language, config.mode, prompts_file)
    check_tool_availability(config)

    # Find all YAML specification files
    spec_files = find_spec_files(config)
    print(f"Found {len(spec_files)} YAML specification files to process")
    print("")

    # Reset token tracking for this run
    from vericoding.core.llm_providers import reset_global_token_stats
    reset_global_token_stats()

    # Process specifications in parallel
    start_time = time.time()
    results = process_files_parallel(config, prompt_loader, llm_provider, spec_files)
    end_time = time.time()
    processing_time = end_time - start_time

    # Finalize wandb run with summary and artifacts
    finalize_wandb_run(wandb_run, config, results, processing_time, args.delete_after_upload, resolved_model)

    # Print summary with reports
    print_summary(config, results, processing_time)
    

if __name__ == "__main__":
    main()
