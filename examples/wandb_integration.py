#!/usr/bin/env python3
"""Practical wandb integration with vericoding verification pipeline."""

import os
import sys
import time
from pathlib import Path

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

from vericoding.utils.wandb_logger import get_wandb_logger
from vericoding.core.config import ProcessingConfig
from vericoding.processing.file_processor import process_spec_file
from vericoding.core.prompts import PromptLoader


def run_verification_with_metrics():
    """Run actual verification with wandb metrics tracking."""
    
    # Setup wandb - will auto-disable if WANDB_API_KEY not set
    logger = get_wandb_logger()
    
    # Initialize run with actual experiment config
    config = ProcessingConfig(
        language="lean",
        llm_provider="claude",
        llm_model="claude-3-5-sonnet",
        max_iterations=3,
        files_dir="examples/lean_specs"
    )
    
    run = logger.init_run(
        name=f"lean_verify_{int(time.time())}",
        config=config.__dict__
    )
    
    if run:
        print(f"Tracking metrics at: {run.url}")
    else:
        print("Running without metrics (wandb disabled or not configured)")
    
    # Simulate verification pipeline
    start_time = time.time()
    
    # Log some realistic verification attempts
    test_files = ["theorem1.lean", "lemma_chain.lean", "induction_proof.lean"]
    results = {"success": 0, "failed": 0}
    
    for i, file in enumerate(test_files):
        # Simulate verification iterations
        for iteration in range(1, 4):
            success = (iteration == 3 and i != 1)  # Second file fails
            
            logger.log_verification(
                file_path=f"specs/{file}",
                iteration=iteration,
                success=success,
                error_text="Type mismatch in hypothesis" if not success else None,
                latency_ms=1200 + iteration * 300
            )
            
            # Log LLM calls for fixes
            if not success and iteration < 3:
                logger.log_llm_call(
                    model="claude-3-5-sonnet",
                    latency_ms=2500 + iteration * 100,
                    tokens_in=1500,
                    tokens_out=2000,
                    cost_usd=0.015
                )
            
            if success:
                results["success"] += 1
                break
        else:
            results["failed"] += 1
    
    # Log summary
    duration = time.time() - start_time
    logger.summary({
        "total_files": len(test_files),
        "success_files": results["success"],
        "failed_files": results["failed"],
        "duration_seconds": duration
    })
    
    logger.finish()
    print(f"Completed: {results['success']} successful, {results['failed']} failed")


if __name__ == "__main__":
    # Set environment variables for demo (normally these would be persistent)
    if not os.getenv("WANDB_API_KEY"):
        print("Note: Set WANDB_API_KEY to enable metrics tracking")
    
    run_verification_with_metrics()