"""Processing modules."""

from .file_processor import (
    ProcessingResult,
    process_spec_file,
    process_files_parallel,
)
from .code_fixer import (
    extract_code,
    verify_spec_preservation,
    restore_specs,
    apply_json_replacements,
)
from ..core.language_tools import verify_file

__all__ = [
    "ProcessingResult",
    "process_spec_file",
    "process_files_parallel",
    "extract_code",
    "verify_spec_preservation",
    "restore_specs",
    "apply_json_replacements",
    "verify_file",
]
