"""Wandb utilities."""

from __future__ import annotations

import os
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional


try:
    import wandb  # type: ignore
except Exception:  # pragma: no cover - wandb might be unavailable in tests
    wandb = None  # type: ignore



def enabled() -> bool:
    """Return True if a wandb run is active."""
    try:
        return bool(wandb and getattr(wandb, "run", None))
    except Exception:
        return False





def log(data: Dict[str, Any]) -> None:
    """Safely log a dict of metrics to wandb (no-op if disabled)."""
    if not enabled():
        return
    try:
        wandb.log(data)
    except Exception:
        # Never let logging break processing
        pass

def log_exception(file_path: str) -> None:
    if not enabled():
        return
    file_key = Path(file_path).stem
    log({
        f"verify/{file_key}/exception": 1,
        "exception_count": 1,
    })


def init_wandb_run(config, no_wandb: bool = False, resolved_model: str = None) -> Optional["wandb.Run"]:
    """Initialize a wandb run with proper configuration."""
    if no_wandb or not os.getenv("WANDB_API_KEY"):
        if no_wandb:
            print("⚠️  Weights & Biases tracking disabled (--no-wandb flag)")
        else:
            print("⚠️  Weights & Biases tracking disabled (WANDB_API_KEY not set)")
        return None
    
    try:
        # Initialize wandb run  
        run_name = f"vericoding_{config.language}_{config.llm}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        wandb_mode = os.getenv("WANDB_MODE", "online")
        # Extract spec_dir and trim to start from "benchmarks" if present
        spec_dir = str(config.files_dir)
        if "benchmarks" in spec_dir:
            spec_dir = "benchmarks" + spec_dir.split("benchmarks", 1)[1]
        
        wandb_config = {
            "spec_dir": spec_dir,
            "language": config.language,
            "llm_model": resolved_model,
            "max_iterations": config.max_iterations,
            "max_workers": config.max_workers,
            "mode": config.mode,
            "wandb_mode": wandb_mode,
        }
        
        wandb_run = wandb.init(
            project=os.getenv("WANDB_PROJECT", "vericoding"),
            entity=os.getenv("WANDB_ENTITY"),
            name=run_name,
            tags=[config.llm],
            mode=wandb_mode
        )
        # Update config with allow_val_change to avoid errors when keys already exist
        wandb.config.update(wandb_config, allow_val_change=True)
        print(f"✅ Weights & Biases tracking enabled: {run_name}")
        if wandb_run:
            print(f"   View at: {wandb_run.url}")
        return wandb_run
    except Exception as e:
        print(f"⚠️  Failed to initialize wandb: {e}")
        return None


def create_iteration_table() -> Optional["wandb.Table"]:
    """Create a table to track verification iterations for a single file."""
    if not enabled():
        return None
    try:
        return wandb.Table(
            columns=[
                "file_path",
                "iteration",
                "success",
                "vc_spec",
                "vc_code",
                "verifier_message",
                "timestamp",
            ]
        )
    except Exception:
        return None


def add_iteration_row(
    table: Optional["wandb.Table"],
    file_path: str,
    iteration: int,
    success: bool,
    vc_spec: str,
    vc_code: str,
    verifier_message: str = "",
) -> None:
    """Add a row to a per-file iteration table."""
    if table is None:
        return
    try:
        table.add_data(
            file_path,
            iteration,
            success,
            vc_spec[:1000],
            vc_code[:1000],
            verifier_message[:500] if verifier_message else ("Success" if success else "Unknown error"),
            time.time(),
        )
    except Exception:
        pass


def log_table_if_any(table: Optional["wandb.Table"], name: str = "verification_iterations") -> None:
    """Log the iteration table to wandb if it has rows."""
    if not enabled() or table is None:
        return
    try:
        if hasattr(table, "data") and len(table.data) > 0:
            log({name: table})
    except Exception:
        pass


def create_file_artifact(name: str, artifact_type: str = "verification_files") -> Optional["wandb.Artifact"]:
    """Create a wandb artifact for storing files."""
    if not enabled():
        return None
    try:
        return wandb.Artifact(name=name, type=artifact_type)
    except Exception:
        return None


def add_files_to_artifact(
    artifact: Optional["wandb.Artifact"], 
    files: list[tuple[str, str]]
) -> None:
    """Add files to artifact. files is list of (file_path, artifact_name) tuples."""
    if artifact is None:
        return
    try:
        for file_path, artifact_name in files:
            if Path(file_path).exists():
                artifact.add_file(file_path, name=artifact_name)
    except Exception:
        pass


def log_artifact(artifact: Optional["wandb.Artifact"]) -> None:
    """Log artifact to wandb if it has files."""
    if not enabled() or artifact is None:
        return
    try:
        # Only log if artifact has files
        if hasattr(artifact, '_manifest') and artifact._manifest and len(artifact._manifest.entries) > 0:
            wandb.log_artifact(artifact)
    except Exception:
        pass


def log_iteration(
    file_path: str,
    iteration: int, 
    success: bool,
    yaml_dict: dict,
    code_output_path: str,
    error_msg: str = "",
    is_final: bool = False,
    artifact: Optional["wandb.Artifact"] = None,
    iterations_data: Optional[list] = None,
) -> None:
    """Log metrics and files for a verification iteration, and optionally append to iterations_data."""
    # Add to iterations_data if provided
    if iterations_data is not None:
        from vericoding.processing.spec_processor import IterationData
        import time
        
        iterations_data.append(IterationData(
            file_path=file_path,
            iteration=iteration,
            success=success,
            vc_spec=yaml_dict.get("vc-spec", ""),
            vc_code=yaml_dict.get("vc-code", ""),
            verifier_message=error_msg,
            timestamp=time.time()
        ))
    
    # Continue with wandb logging if enabled
    if not enabled():
        return
    
    try:
        file_key = Path(file_path).stem
        
        # 1. Log iteration metrics
        metrics = {
            f"verify/{file_key}/iter": iteration,
            f"verify/{file_key}/success": int(success),
        }
        
        # Add failure details if verification failed
        if not success and error_msg:
            metrics.update({
                f"verify/{file_key}/error": error_msg[:200],  # Truncate long errors
                f"verify/{file_key}/error_full": error_msg,   # Full error for analysis
            })
        
        # Add final iteration metrics if this is the last iteration
        if is_final:
            metrics.update({
                f"verify/{file_key}/final_iter": iteration,
                ("success_count" if success else "failure_count"): 1,
            })
        
        log(metrics)
        
        # 3. Add files to artifact (only on final iteration)
        if is_final and artifact is not None and Path(code_output_path).exists():
            add_files_to_artifact(artifact, [
                (code_output_path, f"{file_key}_iter{iteration}.dfy")
            ])
            
    except Exception:
        pass



def _create_failure_analysis_table(failed_results):
    """Create enhanced failure analysis table and log to wandb."""
    if not enabled() or not failed_results:
        return
        
    try:
        # Categorize errors
        error_categories = {}
        failure_table = wandb.Table(columns=[
            "file", "error_category", "error_snippet", 
            "iterations_attempted", "full_error", "timestamp"
        ])
        
        for result in failed_results:
            error_msg = result.error or "Unknown error"
            
            # Simple error categorization
            category = "unknown"
            if "timeout" in error_msg.lower():
                category = "timeout"
            elif "compilation" in error_msg.lower() or "syntax" in error_msg.lower():
                category = "compilation"
            elif "verification" in error_msg.lower() or "prove" in error_msg.lower():
                category = "verification"
            elif "api" in error_msg.lower() or "rate limit" in error_msg.lower():
                category = "api_error"
            elif "memory" in error_msg.lower() or "resource" in error_msg.lower():
                category = "resource"
            
            # Count error categories
            error_categories[category] = error_categories.get(category, 0) + 1
            
            # Determine iterations attempted
            iterations_attempted = len(result.iterations) if result.iterations else 1
            
            # Add to failure table
            file_name = Path(result.spec_yaml_file).name
            failure_table.add_data(
                file_name,
                category,
                error_msg[:200],  # Snippet for table display
                iterations_attempted,
                error_msg[:1000],  # More detail but still truncated
                time.time()
            )
        
        # Log error category counts
        for category, count in error_categories.items():
            wandb.run.summary[f"error_category/{category}"] = count
        
        # Log failure table
        log({"failure_analysis": failure_table})
        
    except Exception:
        # Don't let table creation break the main flow
        pass





def finalize_wandb_run(wandb_run, config, results, processing_time, delete_after_upload: bool = False, resolved_model: str = None):
    """Finalize wandb run with summary metrics and artifact upload."""
    if not wandb_run:
        return
        
    try:
        from vericoding.core.llm_providers import get_global_token_stats
        
        # Calculate basic statistics
        successful = [r for r in results if r.success]
        failed = [r for r in results if not r.success]
        
        # Calculate iteration statistics
        all_iterations = []
        total_llm_calls = 0
        
        for result in results:
            iterations_for_file = len(result.iterations) if result.iterations else 1
            all_iterations.append(iterations_for_file)
            total_llm_calls += iterations_for_file
        
        # Calculate timing statistics
        avg_time_per_file = processing_time / len(results) if results else 0
        
        # Get token usage statistics
        token_stats = get_global_token_stats()
        
        # Basic summary metrics
        wandb.run.summary["total_files"] = len(results)
        wandb.run.summary["successful_files"] = len(successful)
        wandb.run.summary["failed_files"] = len(failed)
        wandb.run.summary["success_rate"] = len(successful) / len(results) if results else 0
        
        # Timing metrics
        wandb.run.summary["duration_seconds"] = processing_time
        wandb.run.summary["avg_time_per_file"] = avg_time_per_file
        
        # Iteration statistics
        if all_iterations:
            wandb.run.summary["avg_iterations"] = sum(all_iterations) / len(all_iterations)
            wandb.run.summary["min_iterations"] = min(all_iterations)
            wandb.run.summary["max_iterations"] = max(all_iterations)
            wandb.run.summary["total_llm_calls"] = total_llm_calls
        
        # Token usage metrics
        wandb.run.summary["total_input_tokens"] = token_stats["input_tokens"]
        wandb.run.summary["total_output_tokens"] = token_stats["output_tokens"]
        
        # LLM configuration context  
        wandb.run.summary["llm_model"] = resolved_model or config.llm
        
        # Create enhanced failure analysis table
        _create_failure_analysis_table(failed)
        
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
            if delete_after_upload:
                try:
                    import shutil
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
