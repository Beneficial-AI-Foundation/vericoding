"""Weights & Biases metrics tracking."""

import os
import tempfile
from pathlib import Path
from typing import Any, Dict, Optional
from contextlib import suppress
import wandb


class WandbLogger:
    """Metrics tracking for verification experiments."""
    
    def __init__(self, enabled: Optional[bool] = None):
        """Initialize logger. Disabled if WANDB_MODE=disabled or wandb not installed."""
        if enabled is None:
            enabled = os.getenv("WANDB_MODE", "online") != "disabled"
        
        self.enabled = enabled and self._check_wandb()
        self.run = None
        self._metrics_cache = {}
        self._iteration_counts = {}
        
    def _check_wandb(self) -> bool:
        """Check if wandb is available and configured."""
        try:
            return wandb is not None and os.getenv("WANDB_API_KEY") is not None
        except:
            return False
    
    def init_run(self, name: Optional[str] = None, config: Optional[Dict[str, Any]] = None):
        """Start a wandb run if enabled."""
        if not self.enabled:
            return None
            
        try:
            self.run = wandb.init(
                project=os.getenv("WANDB_PROJECT", "vericoding"),
                entity=os.getenv("WANDB_ENTITY"),
                name=name,
                config=config or {},
                mode=os.getenv("WANDB_MODE", "online"),  # type: ignore
                reinit=True
            )
            return self.run
        except Exception as e:
            print(f"Warning: Failed to init wandb: {e}")
            self.enabled = False
            return None
    
    def log_verification(self, file_path: str, iteration: int, success: bool, 
                        error_text: Optional[str] = None, latency_ms: Optional[float] = None):
        """Log verification attempt metrics."""
        if not self.enabled or not self.run:
            return
            
        file_key = Path(file_path).stem
        self._iteration_counts[file_key] = iteration
        
        metrics = {
            f"verify/{file_key}/iter": iteration,
            f"verify/{file_key}/success": int(success),
        }
        
        if latency_ms:
            metrics[f"verify/{file_key}/latency_ms"] = latency_ms
            
        if error_text and len(error_text) > 0:
            # Track error patterns
            if "Type mismatch" in error_text:
                metrics[f"errors/{file_key}/type_mismatch"] = 1
            elif "sorry" in error_text.lower():
                metrics[f"errors/{file_key}/incomplete_proof"] = 1
            elif "timeout" in error_text.lower():
                metrics[f"errors/{file_key}/timeout"] = 1
                
        with suppress(Exception):
            wandb.log(metrics)
    
    def log_llm_call(self, model: str, latency_ms: float, tokens_in: Optional[int] = None, 
                     tokens_out: Optional[int] = None, cost_usd: Optional[float] = None):
        """Log LLM API metrics."""
        if not self.enabled or not self.run:
            return
            
        metrics = {
            "llm/calls": 1,
            "llm/latency_ms": latency_ms,
        }
        
        if tokens_in:
            metrics["llm/tokens_in"] = tokens_in
        if tokens_out:
            metrics["llm/tokens_out"] = tokens_out
        if cost_usd:
            metrics["llm/cost_usd"] = cost_usd
            
        # Track cumulative costs
        if "llm/total_cost" not in self._metrics_cache:
            self._metrics_cache["llm/total_cost"] = 0
        self._metrics_cache["llm/total_cost"] += cost_usd or 0
        metrics["llm/total_cost"] = self._metrics_cache["llm/total_cost"]
        
        with suppress(Exception):
            wandb.log(metrics)
    
    def log_artifact(self, name: str, content: str, artifact_type: str = "code"):
        """Log text content as artifact."""
        if not self.enabled or not self.run:
            return
            
        try:
            with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
                f.write(content)
                temp_path = f.name
                
            artifact = wandb.Artifact(name=name, type=artifact_type)
            artifact.add_file(temp_path)
            self.run.log_artifact(artifact)
            
            Path(temp_path).unlink(missing_ok=True)
        except Exception:
            pass  # Artifact logging is non-critical
    
    def summary(self, metrics: Dict[str, Any]):
        """Log final summary metrics."""
        if not self.enabled or not self.run:
            return
            
        # Calculate derived metrics
        total_files = metrics.get("total_files", 0)
        success_files = metrics.get("success_files", 0)
        
        if total_files > 0:
            metrics["success_rate"] = success_files / total_files
            metrics["avg_iterations"] = sum(self._iteration_counts.values()) / len(self._iteration_counts) if self._iteration_counts else 0
            
        with suppress(Exception):
            for key, value in metrics.items():
                if wandb.run:
                    wandb.run.summary[key] = value
    
    def finish(self):
        """Close the wandb run."""
        if self.enabled and self.run:
            with suppress(Exception):
                self.run.finish()
            self.run = None
            self.enabled = False


# Singleton instance
_logger: Optional[WandbLogger] = None


def get_wandb_logger() -> WandbLogger:
    """Get the global wandb logger instance."""
    global _logger
    if _logger is None:
        _logger = WandbLogger()
    return _logger