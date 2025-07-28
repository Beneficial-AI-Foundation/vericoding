"""Lean verification module for VeriCoding."""

from .prompt_loader import PromptLoader
from .prompts import LeanPromptManager, LeanPromptConfig, PromptType
from .lean_agent import LeanAgent, run_lean_agent
from .tracker import LeanExperimentTracker, run_experiment, run_comparison_experiment

# Keep legacy imports for backward compatibility
try:
    from .spec_to_code_lean import process_spec_file, find_lean_files_with_sorry
except ImportError:
    process_spec_file = None
    find_lean_files_with_sorry = None

__all__ = [
    # Modern API
    "LeanAgent",
    "LeanPromptManager", 
    "LeanPromptConfig",
    "LeanExperimentTracker",
    "run_lean_agent",
    "run_experiment",
    "run_comparison_experiment",
    # Legacy API
    "PromptLoader",
    "process_spec_file",
    "find_lean_files_with_sorry"
]