"""
WANDB experiment tracking for Lean verification experiments.
"""
import os
import json
import time
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, asdict
import wandb

from .lean_agent import LeanAgent, AgentState, VerificationStatus


@dataclass
class ExperimentConfig:
    """Configuration for a Lean experiment."""
    name: str
    spec_dir: Path
    use_mcp: bool = True
    max_iterations: int = 5
    max_files: Optional[int] = None
    tags: List[str] = None
    notes: str = ""
    
    def __post_init__(self):
        if self.tags is None:
            self.tags = ["lean", "mcp" if self.use_mcp else "no-mcp"]


@dataclass
class ExperimentResult:
    """Result of a single file experiment."""
    file_name: str
    success: bool
    iterations: int
    total_time: float
    verification_time: float
    errors: int
    warnings: int
    mcp_tools_used: List[str]
    code_length_initial: int
    code_length_final: int
    trace_artifact: Optional[str] = None


class LeanExperimentTracker:
    """Track Lean verification experiments with WANDB."""
    
    def __init__(self, project_name: str | None = None):
        """Initialize the experiment tracker.
        
        Args:
            project_name: WANDB project name. If None, uses
                `WANDB_PROJECT` env var or falls back to "vericoding".
        """
        # Prefer explicit arg, then env, then repo default
        self.project_name = project_name or os.getenv("WANDB_PROJECT", "vericoding")
        self.results: List[ExperimentResult] = []
        self.wandb_enabled = os.getenv("WANDB_API_KEY") is not None
        self.run = None
        self.start_time = None
        
    def start_experiment(self, config: ExperimentConfig):
        """Start a new experiment run.
        
        Args:
            config: Experiment configuration
        """
        self.config = config
        self.start_time = time.time()
        
        if self.wandb_enabled:
            self.run = wandb.init(
                project=self.project_name,
                name=config.name,
                tags=config.tags,
                notes=config.notes,
                config={
                    "spec_dir": str(config.spec_dir),
                    "use_mcp": config.use_mcp,
                    "max_iterations": config.max_iterations,
                    "max_files": config.max_files,
                    "timestamp": datetime.now().isoformat()
                }
            )
        else:
            print("Warning: WANDB_API_KEY not set. Running in offline mode.")
    
    def track_file_experiment(self, agent: LeanAgent, spec_file: Path, state: AgentState):
        """Track results for a single file experiment.
        
        Args:
            agent: The Lean agent used
            spec_file: The specification file
            state: The final agent state
        """
        # Calculate metrics
        with open(spec_file, 'r') as f:
            initial_code = f.read()
        
        total_time = sum(r.duration for r in state.verification_results)
        total_errors = sum(len(r.errors) for r in state.verification_results)
        total_warnings = sum(len(r.warnings) for r in state.verification_results)
        
        result = ExperimentResult(
            file_name=spec_file.name,
            success=state.success,
            iterations=len(state.iterations),
            total_time=total_time,
            verification_time=total_time,  # Could separate generation vs verification
            errors=total_errors,
            warnings=total_warnings,
            mcp_tools_used=state.mcp_tools_used,
            code_length_initial=len(initial_code),
            code_length_final=len(state.final_code) if state.final_code else len(state.current_code)
        )
        
        self.results.append(result)
        
        # Log to WANDB
        if self.wandb_enabled and self.run:
            # Log metrics
            wandb.log({
                "file": result.file_name,
                "success": int(result.success),
                "iterations": result.iterations,
                "total_time": result.total_time,
                "errors": result.errors,
                "warnings": result.warnings,
                "mcp_tools_count": len(result.mcp_tools_used),
                "code_growth": result.code_length_final - result.code_length_initial
            })
            
            # Save conversation trace as artifact
            if state.iterations:
                self._save_trace_artifact(spec_file, state, result)
    
    def _save_trace_artifact(self, spec_file: Path, state: AgentState, result: ExperimentResult):
        """Save detailed trace as WANDB artifact.
        
        Args:
            spec_file: The specification file
            state: The agent state
            result: The experiment result
        """
        # Create trace data
        trace_data = {
            "spec_file": str(spec_file),
            "success": state.success,
            "iterations": state.iterations,
            "verification_results": [
                {
                    "status": r.status.value,
                    "errors": r.errors,
                    "warnings": r.warnings,
                    "duration": r.duration
                }
                for r in state.verification_results
            ],
            "mcp_tools_used": state.mcp_tools_used,
            "initial_code": open(spec_file).read(),
            "final_code": state.final_code or state.current_code
        }
        
        # Save to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(trace_data, f, indent=2)
            trace_file = f.name
        
        # Create artifact
        artifact = wandb.Artifact(
            name=f"trace_{spec_file.stem}_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            type="experiment_trace",
            description=f"Trace for {spec_file.name}"
        )
        artifact.add_file(trace_file)
        
        # Log the artifact
        self.run.log_artifact(artifact)
        
        # Clean up
        Path(trace_file).unlink()
        
        result.trace_artifact = artifact.name
    
    def finish_experiment(self):
        """Finish the experiment and generate summary."""
        if not self.results:
            print("No results to summarize")
            return
        
        # Calculate summary statistics
        total_files = len(self.results)
        successful = sum(1 for r in self.results if r.success)
        
        summary = {
            "total_files": total_files,
            "successful": successful,
            "failed": total_files - successful,
            "success_rate": successful / total_files if total_files > 0 else 0,
            "avg_iterations": sum(r.iterations for r in self.results) / total_files,
            "avg_time": sum(r.total_time for r in self.results) / total_files,
            "total_time": time.time() - self.start_time,
            "mcp_tools_used": list(set(
                tool for r in self.results for tool in r.mcp_tools_used
            ))
        }
        
        # Log summary to WANDB
        if self.wandb_enabled and self.run:
            wandb.summary.update(summary)
            
            # Create summary artifact
            summary_artifact = wandb.Artifact(
                name=f"summary_{self.config.name}_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                type="experiment_summary"
            )
            
            with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
                json.dump({
                    "config": asdict(self.config),
                    "summary": summary,
                    "results": [asdict(r) for r in self.results]
                }, f, indent=2)
                summary_file = f.name
            
            summary_artifact.add_file(summary_file)
            self.run.log_artifact(summary_artifact)
            
            Path(summary_file).unlink()
            
            # Finish the run
            wandb.finish()
        
        # Print summary
        print("\n=== Experiment Summary ===")
        print(f"Total files: {summary['total_files']}")
        print(f"Successful: {summary['successful']} ({summary['success_rate']*100:.1f}%)")
        print(f"Failed: {summary['failed']}")
        print(f"Average iterations: {summary['avg_iterations']:.2f}")
        print(f"Average time per file: {summary['avg_time']:.2f}s")
        print(f"Total experiment time: {summary['total_time']:.2f}s")
        
        if summary['mcp_tools_used']:
            print(f"MCP tools used: {', '.join(summary['mcp_tools_used'])}")
        
        return summary
    
    def compare_experiments(self, baseline_name: str, mcp_name: str) -> Dict[str, Any]:
        """Compare two experiments (e.g., with and without MCP).
        
        Args:
            baseline_name: Name of baseline experiment
            mcp_name: Name of MCP-enhanced experiment
            
        Returns:
            Comparison statistics
        """
        if not self.wandb_enabled:
            print("WANDB not enabled, cannot compare experiments")
            return {}
        
        api = wandb.Api()
        
        # Fetch runs
        baseline_run = api.run(f"{self.project_name}/{baseline_name}")
        mcp_run = api.run(f"{self.project_name}/{mcp_name}")
        
        # Compare summaries
        comparison = {
            "baseline": {
                "success_rate": baseline_run.summary.get("success_rate", 0),
                "avg_iterations": baseline_run.summary.get("avg_iterations", 0),
                "avg_time": baseline_run.summary.get("avg_time", 0)
            },
            "mcp": {
                "success_rate": mcp_run.summary.get("success_rate", 0),
                "avg_iterations": mcp_run.summary.get("avg_iterations", 0),
                "avg_time": mcp_run.summary.get("avg_time", 0)
            }
        }
        
        # Calculate improvements
        comparison["improvements"] = {
            "success_rate": comparison["mcp"]["success_rate"] - comparison["baseline"]["success_rate"],
            "iteration_reduction": comparison["baseline"]["avg_iterations"] - comparison["mcp"]["avg_iterations"],
            "speedup": comparison["baseline"]["avg_time"] / comparison["mcp"]["avg_time"] if comparison["mcp"]["avg_time"] > 0 else 0
        }
        
        return comparison


def run_experiment(spec_dir: Path, name: str, use_mcp: bool = True, 
                  max_files: Optional[int] = None) -> Dict[str, Any]:
    """Run a complete Lean verification experiment.
    
    Args:
        spec_dir: Directory containing Lean specification files
        name: Name for this experiment
        use_mcp: Whether to use MCP tools
        max_files: Maximum number of files to process
        
    Returns:
        Experiment summary
    """
    # Find Lean files with 'sorry'
    from .spec_to_code_lean import find_lean_files_with_sorry
    files = find_lean_files_with_sorry(spec_dir)
    
    if max_files:
        files = files[:max_files]
    
    if not files:
        print(f"No Lean files with 'sorry' found in {spec_dir}")
        return {}
    
    # Configure experiment
    config = ExperimentConfig(
        name=name,
        spec_dir=spec_dir,
        use_mcp=use_mcp,
        max_files=len(files)
    )
    
    # Initialize tracker and agent
    tracker = LeanExperimentTracker()
    tracker.start_experiment(config)
    
    agent = LeanAgent(use_mcp=use_mcp)
    
    # Process each file
    for i, spec_file in enumerate(files, 1):
        print(f"\n[{i}/{len(files)}] Processing {spec_file.name}...")
        
        try:
            state = agent.process_spec_file(spec_file)
            tracker.track_file_experiment(agent, spec_file, state)
        except Exception as e:
            print(f"Error processing {spec_file.name}: {e}")
            # Log failure
            tracker.results.append(ExperimentResult(
                file_name=spec_file.name,
                success=False,
                iterations=0,
                total_time=0,
                verification_time=0,
                errors=1,
                warnings=0,
                mcp_tools_used=[],
                code_length_initial=0,
                code_length_final=0
            ))
        
        # Small delay to avoid overwhelming the API
        time.sleep(2)
    
    # Finish and get summary
    return tracker.finish_experiment()


def run_comparison_experiment(spec_dir: Path, max_files: Optional[int] = None) -> Dict[str, Any]:
    """Run comparison experiment between baseline and MCP approaches.
    
    Args:
        spec_dir: Directory containing Lean specification files
        max_files: Maximum number of files to process
        
    Returns:
        Comparison results
    """
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Run baseline experiment
    print("=== Running Baseline Experiment (without MCP) ===")
    baseline_name = f"baseline_{timestamp}"
    baseline_summary = run_experiment(spec_dir, baseline_name, use_mcp=False, max_files=max_files)
    
    # Run MCP experiment
    print("\n=== Running MCP-Enhanced Experiment ===")
    mcp_name = f"mcp_{timestamp}"
    mcp_summary = run_experiment(spec_dir, mcp_name, use_mcp=True, max_files=max_files)
    
    # Compare results
    tracker = LeanExperimentTracker()
    comparison = tracker.compare_experiments(baseline_name, mcp_name)
    
    print("\n=== Comparison Results ===")
    print(f"Success rate improvement: {comparison['improvements']['success_rate']*100:.1f}%")
    print(f"Iteration reduction: {comparison['improvements']['iteration_reduction']:.2f}")
    print(f"Speedup: {comparison['improvements']['speedup']:.2f}x")
    
    return comparison
