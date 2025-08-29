
import logging
import sys
import time
from pathlib import Path
from vericoding.core.prompts import init_prompt_loader
from vericoding.utils.wandb_utils import init_wandb_run, finalize_wandb_run
from vericoding.utils.io_utils import parse_command_line_arguments, print_startup_info
    
# Import the modular components
from vericoding.core.config import load_environment, setup_configuration
from vericoding.core.llm_providers import create_llm_provider
from vericoding.core.language_tools import (
    get_tool_path,
    check_tool_availability,
    find_spec_files,
)
from vericoding.processing.spec_processor import process_files_parallel
from vericoding.utils.reporting import print_summary

# Initialize environment and logging
load_environment()
logging.basicConfig(level=logging.INFO, format="%(message)s")

def main():
    """Main entry point for the specification-to-code processing."""

    # Parse command line arguments
    args = parse_command_line_arguments()

    # Set up configuration, wandb run, prompts, LLM provider, and verification tool
    config = setup_configuration(args)
    wandb_run = init_wandb_run(config, args.no_wandb)
    # Use mode-based prompt file selection unless a non-default prompts_file is specified
    prompts_file = None if config.language_config.prompts_file == "prompts.yaml" else config.language_config.prompts_file
    prompt_loader = init_prompt_loader(config.language, config.mode, prompts_file)
    llm_provider = create_llm_provider(config.llm_provider, config.llm_model)
    print_startup_info(config)
    check_tool_availability(config)

    # Find all YAML specification files
    spec_files = find_spec_files(config)
    print(f"Found {len(spec_files)} YAML specification files to process")
    print("")

    # Process specifications in parallel
    start_time = time.time()
    results = process_files_parallel(config, prompt_loader, llm_provider, spec_files)
    end_time = time.time()
    processing_time = end_time - start_time

    # Print summary with reports
    print_summary(config, results, processing_time)
    
    # Finalize wandb run with summary and artifacts
    finalize_wandb_run(wandb_run, config, results, processing_time, args.delete_after_upload)


if __name__ == "__main__":
    main()
