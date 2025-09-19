"""File I/O and thread-safe operations."""

import logging
import threading
import yaml
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

        debug_path = f"debug/{relative_dir}" if str(relative_dir) != "." else "debug"
        logger.info(f"    💾 Saved {phase} code to: {debug_path}/{iteration_file_name}")


def load_postamble_from_yaml(config: ProcessingConfig, lean_file_path: Path) -> str | None:
    """Load the postamble from the corresponding YAML file for unit test mode.
    
    Args:
        config: Processing configuration
        lean_file_path: Path to the Lean file (relative to files_dir)
        
    Returns:
        The postamble content if found, None otherwise
    """
    if config.language != 'lean' or not config.unit_test:
        return None
    
    # Convert from files/ directory to yaml/ directory
    yaml_file_path = lean_file_path.with_suffix('.yaml')
    
    # Look for yaml file in yaml/ subdirectory parallel to files/
    files_dir = Path(config.files_dir)
    
    # If the files_dir ends with 'files', replace with 'yaml'
    if files_dir.name == 'files':
        yaml_dir = files_dir.parent / 'yaml'
    else:
        # Try common patterns: look for yaml/ subdirectory
        yaml_dir = files_dir / 'yaml'
        if not yaml_dir.exists():
            # Alternative: yaml/ directory parallel to current directory
            yaml_dir = files_dir.parent / 'yaml'
    
    full_yaml_path = yaml_dir / yaml_file_path.name
    
    if not full_yaml_path.exists():
        logger.warning(f"    ⚠️ YAML file not found for unit test mode: {full_yaml_path}")
        return None
    
    try:
        with full_yaml_path.open('r', encoding='utf-8') as f:
            yaml_content = yaml.safe_load(f)
        
        postamble = yaml_content.get('vc-postamble', '')
        if postamble:
            logger.info(f"    📋 Loaded postamble from: {full_yaml_path}")
            return postamble.strip()
        else:
            logger.info(f"    📋 No postamble found in: {full_yaml_path}")
            return None
            
    except Exception as e:
        logger.warning(f"    ⚠️ Error loading YAML file {full_yaml_path}: {e}")
        return None
