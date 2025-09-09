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
    
    # Apply limit if specified
    total_files = len(spec_files)
    if args.limit and args.limit > 0:
        spec_files = spec_files[:args.limit]
        print(f"Found {total_files} YAML specification files, processing first {len(spec_files)} (limited by --limit {args.limit})")
    else:
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
    
    # Upload summary files to W&B after they're generated
    if wandb_run:
        try:
            import wandb
            from pathlib import Path
            
            # Upload summary.txt and results.csv as additional files
            summary_file = Path(config.summary_file)
            csv_file = Path(config.output_dir) / "results.csv"
            
            if summary_file.exists():
                wandb.save(str(summary_file))
                print(f"✅ Summary file uploaded to W&B: {summary_file.name}")
            
            if csv_file.exists():
                wandb.save(str(csv_file))
                print(f"✅ Results CSV uploaded to W&B: {csv_file.name}")
                
        except Exception as e:
            print(f"⚠️ Error uploading summary files to W&B: {e}")
    
    # Delete local files after summary generation and W&B upload if requested
    if args.delete_after_upload and wandb_run:
        from pathlib import Path
        import shutil
        
        try:
            output_path = Path(config.output_dir)
            if output_path.exists():
                shutil.rmtree(output_path)
                print(f"🗑️ Local files deleted from {output_path}")
        except Exception as e:
            print(f"⚠️ Error deleting local files: {e}")
    

if __name__ == "__main__":
    main()
