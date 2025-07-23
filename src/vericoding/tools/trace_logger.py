#!/usr/bin/env python3
"""
Trace Logger for VeriCoding Experiments
Captures full conversation traces for debugging and analysis.
"""

import os
import json
import gzip
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Union
from dataclasses import dataclass, asdict, field
import wandb


@dataclass
class ConversationTurn:
    """Single turn in a conversation (user prompt + assistant response)."""
    turn_number: int
    timestamp: str
    prompt: str
    response: str
    tools_used: List[Dict[str, Any]] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class ConversationTrace:
    """Full conversation trace for a single experiment."""
    experiment_id: str
    file_name: str
    language: str
    use_mcp: bool
    start_time: str
    end_time: Optional[str] = None
    turns: List[ConversationTurn] = field(default_factory=list)
    final_code: Optional[str] = None
    verification_results: List[Dict[str, Any]] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


class TraceLogger:
    """Logger for capturing full conversation traces."""
    
    def __init__(self, trace_dir: Optional[Path] = None, 
                 compress: bool = True,
                 use_wandb: bool = True,
                 wandb_project: Optional[str] = None):
        """
        Initialize trace logger.
        
        Args:
            trace_dir: Directory to store traces (default: temp dir if using WANDB)
            compress: Whether to gzip traces to save space
            use_wandb: Whether to upload traces to WANDB artifacts
            wandb_project: WANDB project name (if using WANDB)
        """
        self.use_wandb = use_wandb and os.getenv("WANDB_API_KEY") is not None
        
        if self.use_wandb:
            # Use temp directory for WANDB artifacts
            self.trace_dir = Path(tempfile.mkdtemp(prefix="vericoding_traces_"))
            self.wandb_project = wandb_project or "vericoding-traces"
        else:
            # Use local directory only if not using WANDB
            self.trace_dir = trace_dir or Path.cwd() / "experiment_traces"
            self.trace_dir.mkdir(exist_ok=True)
            
            # Create .gitignore to prevent traces from being committed
            gitignore_path = self.trace_dir / ".gitignore"
            if not gitignore_path.exists():
                with open(gitignore_path, "w") as f:
                    f.write("# Ignore all trace files\n*.json\n*.json.gz\n")
        
        self.compress = compress
        self.active_traces: Dict[str, ConversationTrace] = {}
    
    def start_trace(self, experiment_id: str, file_name: str, 
                   language: str, use_mcp: bool, 
                   metadata: Optional[Dict[str, Any]] = None) -> ConversationTrace:
        """Start a new conversation trace."""
        trace = ConversationTrace(
            experiment_id=experiment_id,
            file_name=file_name,
            language=language,
            use_mcp=use_mcp,
            start_time=datetime.now().isoformat(),
            metadata=metadata or {}
        )
        self.active_traces[experiment_id] = trace
        return trace
    
    def add_turn(self, experiment_id: str, prompt: str, response: str,
                tools_used: Optional[List[Dict[str, Any]]] = None,
                metadata: Optional[Dict[str, Any]] = None):
        """Add a conversation turn to an active trace."""
        if experiment_id not in self.active_traces:
            raise ValueError(f"No active trace for experiment {experiment_id}")
        
        trace = self.active_traces[experiment_id]
        turn = ConversationTurn(
            turn_number=len(trace.turns) + 1,
            timestamp=datetime.now().isoformat(),
            prompt=prompt,
            response=response,
            tools_used=tools_used or [],
            metadata=metadata or {}
        )
        trace.turns.append(turn)
    
    def add_verification_result(self, experiment_id: str, 
                              iteration: int, success: bool,
                              output: str, metadata: Optional[Dict[str, Any]] = None):
        """Add a verification result to the trace."""
        if experiment_id not in self.active_traces:
            raise ValueError(f"No active trace for experiment {experiment_id}")
        
        trace = self.active_traces[experiment_id]
        result = {
            "iteration": iteration,
            "timestamp": datetime.now().isoformat(),
            "success": success,
            "output": output,
            "metadata": metadata or {}
        }
        trace.verification_results.append(result)
    
    def set_final_code(self, experiment_id: str, code: str):
        """Set the final generated code for the experiment."""
        if experiment_id not in self.active_traces:
            raise ValueError(f"No active trace for experiment {experiment_id}")
        
        self.active_traces[experiment_id].final_code = code
    
    def end_trace(self, experiment_id: str, save: bool = True) -> ConversationTrace:
        """End a conversation trace and optionally save it."""
        if experiment_id not in self.active_traces:
            raise ValueError(f"No active trace for experiment {experiment_id}")
        
        trace = self.active_traces[experiment_id]
        trace.end_time = datetime.now().isoformat()
        
        if save:
            self.save_trace(trace)
        
        # Remove from active traces
        del self.active_traces[experiment_id]
        return trace
    
    def save_trace(self, trace: ConversationTrace):
        """Save a trace, uploading to WANDB if enabled."""
        # Create filename with timestamp and experiment details
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"trace_{trace.language}_{trace.file_name}_{timestamp}_{trace.experiment_id}"
        
        # Always save to disk first (temp dir if using WANDB)
        if self.compress:
            filepath = self.trace_dir / f"{filename}.json.gz"
            with gzip.open(filepath, "wt", encoding="utf-8") as f:
                json.dump(asdict(trace), f, indent=2)
        else:
            filepath = self.trace_dir / f"{filename}.json"
            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(asdict(trace), f, indent=2)
        
        # Upload to WANDB if enabled
        if self.use_wandb:
            try:
                # Initialize a new WANDB run for trace upload
                run = wandb.init(
                    project=self.wandb_project,
                    name=f"trace_{trace.experiment_id}",
                    tags=["trace", trace.language, "mcp" if trace.use_mcp else "no-mcp"],
                    config={
                        "experiment_id": trace.experiment_id,
                        "file_name": trace.file_name,
                        "language": trace.language,
                        "use_mcp": trace.use_mcp,
                        "total_turns": len(trace.turns),
                    }
                )
                
                # Create artifact
                artifact = wandb.Artifact(
                    name=f"trace_{trace.experiment_id}",
                    type="experiment_trace",
                    description=f"Conversation trace for {trace.file_name}",
                    metadata={
                        "language": trace.language,
                        "use_mcp": trace.use_mcp,
                        "success": trace.verification_results[-1]["success"] if trace.verification_results else None,
                        "total_turns": len(trace.turns),
                        "timestamp": timestamp
                    }
                )
                
                # Add the trace file
                artifact.add_file(str(filepath))
                
                # Also create and add a summary report
                summary = self.create_trace_summary(trace)
                summary_path = filepath.parent / f"{filename}_summary.json"
                with open(summary_path, "w") as f:
                    json.dump(summary, f, indent=2)
                artifact.add_file(str(summary_path))
                
                # Create and add markdown report
                report = self.create_markdown_report(trace)
                report_path = filepath.parent / f"{filename}_report.md"
                with open(report_path, "w") as f:
                    f.write(report)
                artifact.add_file(str(report_path))
                
                # Log the artifact
                run.log_artifact(artifact)
                
                # Log summary metrics
                wandb.log(summary)
                
                # Finish the run
                wandb.finish()
                
                print(f"Trace uploaded to WANDB: {artifact.name}")
                
            except Exception as e:
                print(f"Warning: Failed to upload trace to WANDB: {e}")
                print(f"Trace saved locally to {filepath}")
        else:
            print(f"Trace saved to {filepath}")
    
    def load_trace(self, filepath: Union[str, Path]) -> ConversationTrace:
        """Load a trace from disk."""
        filepath = Path(filepath)
        
        if filepath.suffix == ".gz":
            with gzip.open(filepath, "rt", encoding="utf-8") as f:
                data = json.load(f)
        else:
            with open(filepath, "r", encoding="utf-8") as f:
                data = json.load(f)
        
        # Convert back to ConversationTrace
        trace = ConversationTrace(**data)
        trace.turns = [ConversationTurn(**turn) for turn in trace.turns]
        return trace
    
    def create_trace_summary(self, trace: ConversationTrace) -> Dict[str, Any]:
        """Create a summary of a trace for quick analysis."""
        return {
            "experiment_id": trace.experiment_id,
            "file_name": trace.file_name,
            "language": trace.language,
            "use_mcp": trace.use_mcp,
            "total_turns": len(trace.turns),
            "total_tools_used": sum(len(turn.tools_used) for turn in trace.turns),
            "verification_attempts": len(trace.verification_results),
            "final_success": trace.verification_results[-1]["success"] if trace.verification_results else False,
            "duration": self._calculate_duration(trace.start_time, trace.end_time),
            "unique_tools": list(set(
                tool["name"] for turn in trace.turns 
                for tool in turn.tools_used if "name" in tool
            )),
            "prompt_lengths": [len(turn.prompt) for turn in trace.turns],
            "response_lengths": [len(turn.response) for turn in trace.turns],
            "total_tokens_estimate": sum(
                len(turn.prompt) + len(turn.response) for turn in trace.turns
            ) // 4,  # Rough token estimate
        }
    
    def _calculate_duration(self, start_time: str, end_time: Optional[str]) -> float:
        """Calculate duration between timestamps in seconds."""
        if not end_time:
            return 0.0
        
        start = datetime.fromisoformat(start_time)
        end = datetime.fromisoformat(end_time)
        return (end - start).total_seconds()
    
    def create_markdown_report(self, trace: ConversationTrace) -> str:
        """Create a human-readable markdown report of a trace."""
        summary = self.create_trace_summary(trace)
        
        report = f"""# Experiment Trace Report

## Experiment Details
- **ID**: {trace.experiment_id}
- **File**: {trace.file_name}
- **Language**: {trace.language}
- **MCP Enabled**: {trace.use_mcp}
- **Duration**: {summary['duration']:.2f} seconds
- **Total Turns**: {summary['total_turns']}
- **Final Success**: {summary['final_success']}

## Conversation Flow

"""
        
        for turn in trace.turns:
            report += f"### Turn {turn.turn_number} ({turn.timestamp})\n\n"
            report += f"**Prompt**:\n```\n{turn.prompt}\n```\n\n"
            
            if turn.tools_used:
                report += "**Tools Used**:\n"
                for tool in turn.tools_used:
                    report += f"- {tool.get('name', 'Unknown')}"
                    if 'parameters' in tool:
                        report += f" with params: {json.dumps(tool['parameters'], indent=2)}"
                    report += "\n"
                report += "\n"
            
            report += f"**Response**:\n```\n{turn.response}\n```\n\n"
            report += "---\n\n"
        
        if trace.verification_results:
            report += "## Verification Results\n\n"
            for i, result in enumerate(trace.verification_results):
                report += f"### Attempt {i+1}\n"
                report += f"- **Success**: {result['success']}\n"
                report += f"- **Output**: \n```\n{result['output']}\n```\n\n"
        
        if trace.final_code:
            report += "## Final Generated Code\n\n"
            report += f"```{trace.language}\n{trace.final_code}\n```\n"
        
        return report


# Global trace logger instance
_global_trace_logger = None


def get_trace_logger(use_wandb: bool = True) -> TraceLogger:
    """Get or create the global trace logger instance."""
    global _global_trace_logger
    if _global_trace_logger is None:
        _global_trace_logger = TraceLogger(use_wandb=use_wandb)
    return _global_trace_logger


def set_trace_logger(logger: TraceLogger):
    """Set the global trace logger instance."""
    global _global_trace_logger
    _global_trace_logger = logger