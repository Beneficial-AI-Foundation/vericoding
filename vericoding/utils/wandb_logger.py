"""Weights & Biases integration for experiment tracking."""

import os
from pathlib import Path
from typing import Any, Dict, Optional, List
from dataclasses import dataclass
import wandb
from datetime import datetime


@dataclass
class WandbConfig:
    """Configuration for Weights & Biases integration."""
    
    project: str = "vericoding"
    entity: Optional[str] = None
    tags: Optional[List[str]] = None
    notes: Optional[str] = None
    mode: str = "online"  # online, offline, or disabled
    save_code: bool = True
    log_frequency: int = 100
    
    @classmethod
    def from_env(cls) -> "WandbConfig":
        """Create config from environment variables."""
        return cls(
            project=os.getenv("WANDB_PROJECT", "vericoding"),
            entity=os.getenv("WANDB_ENTITY"),
            mode=os.getenv("WANDB_MODE", "online"),
            save_code=os.getenv("WANDB_SAVE_CODE", "true").lower() == "true",
        )


class WandbLogger:
    """Handles Weights & Biases logging for vericoding experiments."""
    
    def __init__(self, config: Optional[WandbConfig] = None):
        """Initialize the wandb logger."""
        self.config = config or WandbConfig.from_env()
        self.run = None
        self._initialized = False
        
    def init_run(
        self,
        name: Optional[str] = None,
        config: Optional[Dict[str, Any]] = None,
        resume: Optional[str] = None,
        **kwargs
    ) -> wandb.Run:
        """Initialize a new wandb run."""
        if self._initialized and self.run:
            return self.run
            
        # Merge configurations
        wandb_config = {
            "project": self.config.project,
            "entity": self.config.entity,
            "tags": self.config.tags,
            "notes": self.config.notes,
            "mode": self.config.mode,
            "save_code": self.config.save_code,
        }
        wandb_config.update(kwargs)
        
        # Initialize run
        self.run = wandb.init(
            name=name or f"vericoding_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            config=config,
            resume=resume,
            **wandb_config
        )
        self._initialized = True
        return self.run
    
    def log_file_processing(
        self,
        file_path: str,
        language: str,
        status: str,
        iteration: int = 0,
        error: Optional[str] = None,
        metrics: Optional[Dict[str, Any]] = None
    ):
        """Log file processing information."""
        if not self._initialized:
            return
            
        log_data = {
            "file": str(Path(file_path).name),
            "language": language,
            "status": status,
            "iteration": iteration,
            "timestamp": datetime.now().isoformat(),
        }
        
        if error:
            log_data["error"] = error
            
        if metrics:
            log_data.update(metrics)
            
        wandb.log(log_data)
    
    def log_verification_attempt(
        self,
        file_path: str,
        iteration: int,
        success: bool,
        verification_output: str,
        fix_applied: Optional[str] = None,
        error_count: int = 0
    ):
        """Log verification attempt details."""
        if not self._initialized:
            return
            
        log_data = {
            f"verification/{Path(file_path).stem}/iteration": iteration,
            f"verification/{Path(file_path).stem}/success": success,
            f"verification/{Path(file_path).stem}/error_count": error_count,
        }
        
        if fix_applied:
            log_data[f"verification/{Path(file_path).stem}/fix_type"] = fix_applied
            
        wandb.log(log_data)
        
        # Log verification output as text artifact if significant
        if len(verification_output) > 100:
            self.log_text_artifact(
                f"verification_output_{Path(file_path).stem}_iter{iteration}",
                verification_output,
                metadata={"iteration": iteration, "success": success}
            )
    
    def log_llm_call(
        self,
        prompt_type: str,
        model: str,
        input_tokens: Optional[int] = None,
        output_tokens: Optional[int] = None,
        latency_ms: Optional[float] = None,
        cost: Optional[float] = None
    ):
        """Log LLM API call metrics."""
        if not self._initialized:
            return
            
        log_data = {
            f"llm/{prompt_type}/calls": 1,
            f"llm/{prompt_type}/model": model,
        }
        
        if input_tokens:
            log_data[f"llm/{prompt_type}/input_tokens"] = input_tokens
        if output_tokens:
            log_data[f"llm/{prompt_type}/output_tokens"] = output_tokens
        if latency_ms:
            log_data[f"llm/{prompt_type}/latency_ms"] = latency_ms
        if cost:
            log_data[f"llm/{prompt_type}/cost_usd"] = cost
            
        wandb.log(log_data)
    
    def log_experiment_summary(
        self,
        total_files: int,
        successful_files: int,
        failed_files: int,
        bypassed_files: int,
        total_iterations: int,
        total_llm_calls: int,
        duration_seconds: float
    ):
        """Log experiment summary statistics."""
        if not self._initialized:
            return
            
        summary = {
            "summary/total_files": total_files,
            "summary/successful_files": successful_files,
            "summary/failed_files": failed_files,
            "summary/bypassed_files": bypassed_files,
            "summary/success_rate": successful_files / total_files if total_files > 0 else 0,
            "summary/total_iterations": total_iterations,
            "summary/avg_iterations_per_file": total_iterations / total_files if total_files > 0 else 0,
            "summary/total_llm_calls": total_llm_calls,
            "summary/duration_seconds": duration_seconds,
            "summary/files_per_minute": (total_files / duration_seconds) * 60 if duration_seconds > 0 else 0,
        }
        
        wandb.log(summary)
        
        # Also set as summary metrics
        for key, value in summary.items():
            wandb.run.summary[key] = value
    
    def log_code_artifact(
        self,
        file_path: str,
        code: str,
        version: str,
        metadata: Optional[Dict[str, Any]] = None
    ):
        """Log code as a wandb artifact."""
        if not self._initialized:
            return
            
        # Determine file extension based on original file
        ext = Path(file_path).suffix or ".lean"
        artifact_name = f"code_{Path(file_path).stem}_{version}"
        
        artifact = wandb.Artifact(
            name=artifact_name,
            type="lean_code" if ext == ".lean" else "code",
            metadata=metadata or {}
        )
        
        # Save code to temporary file with proper extension
        temp_path = Path(f"/tmp/{artifact_name}{ext}")
        temp_path.write_text(code)
        
        # Add to artifact
        artifact.add_file(str(temp_path))
        
        # Log artifact
        wandb.log_artifact(artifact)
        
        # Clean up
        temp_path.unlink()
    
    def log_text_artifact(
        self,
        name: str,
        text: str,
        metadata: Optional[Dict[str, Any]] = None
    ):
        """Log text content as a wandb artifact."""
        if not self._initialized:
            return
            
        artifact = wandb.Artifact(
            name=name,
            type="text",
            metadata=metadata or {}
        )
        
        # Save text to temporary file
        temp_path = Path(f"/tmp/{name}.txt")
        temp_path.write_text(text)
        
        # Add to artifact
        artifact.add_file(str(temp_path))
        
        # Log artifact
        wandb.log_artifact(artifact)
        
        # Clean up
        temp_path.unlink()
    
    def log_config(self, config: Any):
        """Log configuration object to wandb."""
        if not self._initialized:
            return
            
        # Convert config to dict if it's a dataclass or has __dict__
        if hasattr(config, "__dict__"):
            config_dict = {}
            for key, value in config.__dict__.items():
                if hasattr(value, "__dict__"):
                    # Handle nested configs
                    config_dict[key] = {k: str(v) for k, v in value.__dict__.items()}
                else:
                    config_dict[key] = str(value)
        else:
            config_dict = config
            
        wandb.config.update(config_dict)
    
    def finish(self):
        """Finish the wandb run."""
        if self._initialized and self.run:
            self.run.finish()
            self._initialized = False
            self.run = None
    
    def __enter__(self):
        """Context manager entry."""
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.finish()


# Global logger instance
_global_logger: Optional[WandbLogger] = None


def get_wandb_logger() -> WandbLogger:
    """Get or create the global wandb logger instance."""
    global _global_logger
    if _global_logger is None:
        _global_logger = WandbLogger()
    return _global_logger


def init_wandb_run(**kwargs) -> wandb.Run:
    """Initialize a wandb run using the global logger."""
    logger = get_wandb_logger()
    return logger.init_run(**kwargs)