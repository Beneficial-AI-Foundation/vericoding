"""File I/O and thread-safe operations."""

import logging
import threading
from pathlib import Path

from ..core.config import ProcessingConfig

# Set up a basic logger
logging.basicConfig(level=logging.INFO, format="%(message)s")
logger = logging.getLogger(__name__)

# Module-level thread safety locks (need to be shared across all instances)
_file_write_lock = threading.Lock()


def file_write_lock():
    """Return the file write lock for thread-safe file operations."""
    return _file_write_lock


def save_iteration_code(
    config: ProcessingConfig, relative_path: Path, iteration: int, code: str, phase: str
):
    """Save code after each iteration for debugging."""
    if not config.debug_mode:
        return

    base_name = relative_path.stem

    if phase in ["original", "generated", "current"]:
        iteration_file_name = f"{base_name}_iter_{iteration}_{phase}{config.language_config.file_extension}"

        relative_dir = relative_path.parent
        # Save debug files in a separate 'debug' subdirectory
        debug_output_subdir = (
            Path(config.output_dir) / "debug" / relative_dir
            if str(relative_dir) != "."
            else Path(config.output_dir) / "debug"
        )

        with _file_write_lock:
            debug_output_subdir.mkdir(parents=True, exist_ok=True)
            iteration_path = debug_output_subdir / iteration_file_name
            with iteration_path.open("w") as f:
                f.write(code)

        logger.info(
            f"    💾 Saved {phase} code to: debug/{relative_dir}/{iteration_file_name}"
            if str(relative_dir) != "."
            else f"    💾 Saved {phase} code to: debug/{iteration_file_name}"
        )
