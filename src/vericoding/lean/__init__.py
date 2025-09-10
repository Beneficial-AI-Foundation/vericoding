"""Lean verification module for VeriCoding.

This package uses lazy imports to avoid heavy dependencies at import time.
Modules are loaded on first attribute access.
"""

from importlib import import_module
from typing import Any

__all__ = [
    # Modern API (lazily imported)
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
    "find_lean_files_with_sorry",
]


_LAZY_MAP = {
    # Modern API
    "LeanAgent": (".lean_agent", "LeanAgent"),
    "run_lean_agent": (".lean_agent", "run_lean_agent"),
    "LeanPromptManager": (".prompts", "LeanPromptManager"),
    "LeanPromptConfig": (".prompts", "LeanPromptConfig"),
    "LeanExperimentTracker": (".tracker", "LeanExperimentTracker"),
    "run_experiment": (".tracker", "run_experiment"),
    "run_comparison_experiment": (".tracker", "run_comparison_experiment"),
    # Legacy API
    "PromptLoader": (".prompt_loader", "PromptLoader"),
    "process_spec_file": (".spec_to_code_lean", "process_spec_file"),
    "find_lean_files_with_sorry": (".spec_to_code_lean", "find_lean_files_with_sorry"),
}


def __getattr__(name: str) -> Any:
    if name in _LAZY_MAP:
        mod_name, attr = _LAZY_MAP[name]
        mod = import_module(mod_name, __name__)
        return getattr(mod, attr)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
