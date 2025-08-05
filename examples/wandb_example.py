#!/usr/bin/env python3
"""Example script showing how to use wandb with vericoding for experiment tracking."""

import os
import sys
from pathlib import Path

# Add parent directory to path to import vericoding
sys.path.append(str(Path(__file__).parent.parent))

from vericoding.utils.wandb_logger import WandbConfig, WandbLogger, init_wandb_run

def main():
    """Example of using wandb logging for vericoding experiments."""
    
    # Configure wandb
    wandb_config = WandbConfig(
        project="vericoding-experiments",
        entity=None,  # Will use default from WANDB_ENTITY env var
        tags=["lean", "experiment", "example"],
        notes="Example experiment with Lean code verification",
        mode="online",  # or "offline" for local logging
        save_code=True
    )
    
    # Initialize logger
    logger = WandbLogger(wandb_config)
    
    # Initialize run with experiment configuration
    run = logger.init_run(
        name="lean_verification_example",
        config={
            "language": "lean",
            "max_iterations": 5,
            "llm_provider": "claude",
            "llm_model": "claude-3-5-sonnet",
            "files": ["example1.lean", "example2.lean"]
        }
    )
    
    print(f"Started wandb run: {run.name}")
    print(f"View at: {run.url}")
    
    # Example: Log file processing
    logger.log_file_processing(
        file_path="examples/example1.lean",
        language="lean",
        status="started",
        iteration=0
    )
    
    # Example: Log LLM call
    logger.log_llm_call(
        prompt_type="generate_code",
        model="claude-3-5-sonnet",
        input_tokens=1500,
        output_tokens=2000,
        latency_ms=3500.5,
        cost=0.024
    )
    
    # Example: Log verification attempt
    logger.log_verification_attempt(
        file_path="examples/example1.lean",
        iteration=1,
        success=False,
        verification_output="Error: Type mismatch at line 42",
        error_count=1
    )
    
    # Example: Log Lean code artifact
    lean_code = """
import Mathlib.Data.List.Basic

theorem example_theorem (l : List Nat) : l.reverse.reverse = l := by
  sorry
"""
    
    logger.log_code_artifact(
        file_path="examples/example1.lean",
        code=lean_code,
        version="generated",
        metadata={
            "language": "lean4",
            "theorem_count": 1,
            "has_sorry": True
        }
    )
    
    # Example: Log another verification attempt (successful)
    logger.log_verification_attempt(
        file_path="examples/example1.lean", 
        iteration=2,
        success=True,
        verification_output="All theorems verified successfully",
        error_count=0
    )
    
    # Example: Log file completion
    logger.log_file_processing(
        file_path="examples/example1.lean",
        language="lean",
        status="success",
        iteration=2,
        metrics={
            "total_iterations": 2,
            "theorem_count": 1,
            "lines_of_code": 5
        }
    )
    
    # Example: Log experiment summary
    logger.log_experiment_summary(
        total_files=2,
        successful_files=1,
        failed_files=1,
        bypassed_files=0,
        total_iterations=7,
        total_llm_calls=14,
        duration_seconds=125.5
    )
    
    # Finish the run
    logger.finish()
    print("Wandb run completed!")

if __name__ == "__main__":
    main()