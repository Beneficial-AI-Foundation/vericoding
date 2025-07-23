#!/usr/bin/env python3
"""
Experiment Tracker for VeriCoding
Tracks and compares performance of spec-to-code generation with and without MCP tools.
"""

import os
import time
import json
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any
import wandb
from dataclasses import dataclass, asdict


@dataclass
class ExperimentResult:
    """Result of a single spec-to-code experiment."""
    file_name: str
    language: str  # "dafny", "verus", or "lean"
    use_mcp: bool
    success: bool
    iterations: int
    total_time: float
    verification_time: float
    api_calls: int
    error: Optional[str] = None
    metadata: Optional[Dict[str, Any]] = None


class ExperimentTracker:
    """Track experiments and log to WANDB."""
    
    def __init__(self, project_name: str = "vericoding-experiments", 
                 run_name: Optional[str] = None,
                 tags: Optional[List[str]] = None):
        """Initialize experiment tracker with WANDB."""
        self.project_name = project_name
        self.run_name = run_name or f"run_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        self.tags = tags or []
        
        # Initialize WANDB if API key is set
        if os.getenv("WANDB_API_KEY"):
            wandb.init(
                project=self.project_name,
                name=self.run_name,
                tags=self.tags,
                config={
                    "mcp_enabled": self._is_mcp_enabled(),
                    "languages": ["dafny", "verus", "lean"],
                    "timestamp": datetime.now().isoformat()
                }
            )
            self.wandb_enabled = True
        else:
            print("Warning: WANDB_API_KEY not set. Running in offline mode.")
            self.wandb_enabled = False
        
        self.results: List[ExperimentResult] = []
        self.start_time = time.time()
    
    def _is_mcp_enabled(self) -> bool:
        """Check if MCP is enabled by looking for .mcp.json file."""
        mcp_file = Path.cwd() / ".mcp.json"
        return mcp_file.exists()
    
    def log_experiment(self, result: ExperimentResult):
        """Log a single experiment result."""
        self.results.append(result)
        
        if self.wandb_enabled:
            # Log to WANDB
            wandb.log({
                "file_name": result.file_name,
                "language": result.language,
                "use_mcp": result.use_mcp,
                "success": int(result.success),
                "iterations": result.iterations,
                "total_time": result.total_time,
                "verification_time": result.verification_time,
                "api_calls": result.api_calls,
                "error": result.error or "",
            })
    
    def compare_results(self, baseline_results: List[ExperimentResult], 
                       mcp_results: List[ExperimentResult]) -> Dict[str, Any]:
        """Compare baseline (non-MCP) results with MCP results."""
        comparison = {}
        
        for language in ["dafny", "verus", "lean"]:
            baseline_lang = [r for r in baseline_results if r.language == language]
            mcp_lang = [r for r in mcp_results if r.language == language]
            
            if not baseline_lang or not mcp_lang:
                continue
            
            # Calculate metrics
            baseline_success_rate = sum(r.success for r in baseline_lang) / len(baseline_lang)
            mcp_success_rate = sum(r.success for r in mcp_lang) / len(mcp_lang)
            
            baseline_avg_iterations = sum(r.iterations for r in baseline_lang) / len(baseline_lang)
            mcp_avg_iterations = sum(r.iterations for r in mcp_lang) / len(mcp_lang)
            
            baseline_avg_time = sum(r.total_time for r in baseline_lang) / len(baseline_lang)
            mcp_avg_time = sum(r.total_time for r in mcp_lang) / len(mcp_lang)
            
            comparison[language] = {
                "baseline_success_rate": baseline_success_rate,
                "mcp_success_rate": mcp_success_rate,
                "success_rate_improvement": mcp_success_rate - baseline_success_rate,
                "baseline_avg_iterations": baseline_avg_iterations,
                "mcp_avg_iterations": mcp_avg_iterations,
                "iteration_reduction": baseline_avg_iterations - mcp_avg_iterations,
                "baseline_avg_time": baseline_avg_time,
                "mcp_avg_time": mcp_avg_time,
                "time_reduction": baseline_avg_time - mcp_avg_time,
                "speedup": baseline_avg_time / mcp_avg_time if mcp_avg_time > 0 else 0,
            }
        
        return comparison
    
    def save_results(self, output_dir: Optional[Path] = None):
        """Save experiment results to JSON file."""
        if output_dir is None:
            output_dir = Path.cwd() / "experiment_results"
        
        output_dir.mkdir(exist_ok=True)
        
        # Save raw results
        results_file = output_dir / f"results_{self.run_name}.json"
        with open(results_file, "w") as f:
            json.dump([asdict(r) for r in self.results], f, indent=2)
        
        # Save summary
        summary = {
            "run_name": self.run_name,
            "total_experiments": len(self.results),
            "total_time": time.time() - self.start_time,
            "languages": list(set(r.language for r in self.results)),
            "mcp_experiments": sum(1 for r in self.results if r.use_mcp),
            "non_mcp_experiments": sum(1 for r in self.results if not r.use_mcp),
            "overall_success_rate": sum(r.success for r in self.results) / len(self.results) if self.results else 0,
        }
        
        summary_file = output_dir / f"summary_{self.run_name}.json"
        with open(summary_file, "w") as f:
            json.dump(summary, f, indent=2)
        
        print(f"Results saved to {results_file}")
        print(f"Summary saved to {summary_file}")
    
    def finish(self):
        """Finish tracking and close WANDB run."""
        if self.wandb_enabled:
            # Log final summary
            wandb.summary["total_experiments"] = len(self.results)
            wandb.summary["total_time"] = time.time() - self.start_time
            wandb.summary["overall_success_rate"] = (
                sum(r.success for r in self.results) / len(self.results) 
                if self.results else 0
            )
            
            wandb.finish()
        
        # Save results locally
        self.save_results()


def run_comparison_experiment(spec_dirs: Dict[str, Path], 
                            max_iterations: int = 5) -> Dict[str, Any]:
    """
    Run a comparison experiment between baseline and MCP approaches.
    
    Args:
        spec_dirs: Dictionary mapping language names to spec directories
        max_iterations: Maximum iterations for each experiment
    
    Returns:
        Comparison results
    """
    from vericoding.lean.spec_to_code_lean_sdk import process_spec_file_with_mcp
    
    # Run baseline experiments (without MCP)
    print("Running baseline experiments (without MCP)...")
    baseline_tracker = ExperimentTracker(
        run_name="baseline_no_mcp",
        tags=["baseline", "no_mcp"]
    )
    
    for language, spec_dir in spec_dirs.items():
        if language == "lean" and spec_dir.exists():
            # Run Lean experiments without MCP
            from vericoding.lean.spec_to_code_lean import process_spec_file, find_lean_files_with_sorry
            
            files = find_lean_files_with_sorry(spec_dir)
            for file in files:
                start_time = time.time()
                result = process_spec_file(file, api_timeout=120, api_delay=2.0)
                
                baseline_tracker.log_experiment(ExperimentResult(
                    file_name=file.name,
                    language="lean",
                    use_mcp=False,
                    success=result["success"],
                    iterations=result["nr_iter"],
                    total_time=time.time() - start_time,
                    verification_time=0,  # TODO: track this separately
                    api_calls=result["nr_iter"],  # Approximation
                    error=result.get("error")
                ))
    
    baseline_tracker.finish()
    
    # Run MCP experiments
    print("\nRunning MCP experiments...")
    mcp_tracker = ExperimentTracker(
        run_name="with_mcp",
        tags=["mcp", "lean-lsp-mcp"]
    )
    
    for language, spec_dir in spec_dirs.items():
        if language == "lean" and spec_dir.exists():
            # Run Lean experiments with MCP
            files = find_lean_files_with_sorry(spec_dir)
            for file in files:
                start_time = time.time()
                result = process_spec_file_with_mcp(file, max_iterations=max_iterations)
                
                mcp_tracker.log_experiment(ExperimentResult(
                    file_name=file.name,
                    language="lean",
                    use_mcp=True,
                    success=result["success"],
                    iterations=result["iterations"],
                    total_time=time.time() - start_time,
                    verification_time=result.get("verification_time", 0),
                    api_calls=result["iterations"],
                    error=result.get("error")
                ))
    
    mcp_tracker.finish()
    
    # Compare results
    comparison = mcp_tracker.compare_results(
        baseline_tracker.results,
        mcp_tracker.results
    )
    
    return comparison


if __name__ == "__main__":
    # Example usage
    spec_dirs = {
        "lean": Path("./NumpySpec/DafnySpecs"),
    }
    
    results = run_comparison_experiment(spec_dirs, max_iterations=5)
    print("\nComparison Results:")
    print(json.dumps(results, indent=2))