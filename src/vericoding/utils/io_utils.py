"""File I/O and thread-safe operations."""

import argparse
import logging
import threading
from pathlib import Path

import yaml
from typing import Tuple

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
    config: ProcessingConfig, 
    relative_path: Path | None, 
    iteration: int, 
    code: str, 
    phase: str,
    verification_file_path: str | None = None,
    source_file_path: Path | None = None,
):
    """Write current iteration code to the verification file (if provided) and
    save a debug snapshot when debug_mode is enabled.
    If relative_path is None and source_file_path is provided, compute relative_path from config.files_dir.
    """
    # Always write the main verification file if a path is provided
    if verification_file_path:
        with open(verification_file_path, "w") as f:
            f.write(code)

    # Determine relative_path for debug outputs
    if relative_path is None and source_file_path is not None:
        try:
            relative_path = source_file_path.relative_to(Path(config.files_dir))
        except Exception:
            # Fallback: just use the file name
            relative_path = Path(source_file_path.name)

    # Debug snapshots only when debug_mode is enabled
    if not config.debug_mode or relative_path is None:
        return

    base_name = relative_path.stem

    if phase in ["original", "generated", "current"]:
        iteration_file_name = f"{base_name}_iter_{iteration}_{phase}{config.language_config.output_extension}"

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


def prepare_output_paths(
    config: ProcessingConfig, source_file_path: Path
) -> tuple[Path, Path, str]:
    """Ensure output directory exists and return (yaml_output_path, code_output_path, verification_file_path)."""
    try:
        relative_path = source_file_path.relative_to(Path(config.files_dir))
    except Exception:
        relative_path = Path(source_file_path.name)
    base_file_name = source_file_path.stem

    relative_dir = relative_path.parent
    output_subdir = (
        Path(config.output_dir) / relative_dir
        if str(relative_dir) != "."
        else Path(config.output_dir)
    )

    with _file_write_lock:
        output_subdir.mkdir(parents=True, exist_ok=True)

    yaml_output_path = output_subdir / f"{base_file_name}_impl.yaml"
    code_output_path = output_subdir / f"{base_file_name}_impl{config.language_config.output_extension}"
    return yaml_output_path, code_output_path, str(code_output_path)


def parse_command_line_arguments():
    available_languages = ProcessingConfig.get_available_languages()

    parser = argparse.ArgumentParser(
        description="Unified Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(available_languages.keys())}
Supported LLM providers: claude, gpt, o1, gemini, grok, deepseek, glm, mistral, openrouter

Examples:
  python spec_to_code.py dafny ./specs  # Uses Claude Opus 4.1 (Aug 2025, best for reasoning)
  python spec_to_code.py lean ./NumpySpec/DafnySpecs --iterations 3
  python spec_to_code.py verus ./benchmarks/verus_specs --debug --iterations 5
  
  # Easy provider switching (all use OpenRouter with one API key):
  python spec_to_code.py dafny ./specs --llm-provider claude    # Claude Opus 4.1 (Aug 2025)
  python spec_to_code.py dafny ./specs --llm-provider gpt       # GPT-5 (Aug 2025)
  python spec_to_code.py dafny ./specs --llm-provider o1        # O1 reasoning model
  python spec_to_code.py dafny ./specs --llm-provider gemini    # Gemini 2.5 Pro (June 2025)
  python spec_to_code.py dafny ./specs --llm-provider grok      # Grok 4 (July 2025)
  python spec_to_code.py dafny ./specs --llm-provider deepseek  # DeepSeek V3.1 (Aug 2025)
  python spec_to_code.py dafny ./specs --llm-provider glm       # GLM-4.5 Turbo (2025)
  python spec_to_code.py dafny ./specs --llm-provider mistral   # Mistral Large 2 (2025)
  
  # Custom models (override defaults):
  python spec_to_code.py dafny ./specs --llm-provider claude --llm-model anthropic/claude-3.5-haiku
  python spec_to_code.py dafny ./specs --llm-provider gpt --llm-model openai/o1-preview
  python spec_to_code.py dafny ./specs --output-folder /path/to/results
  python spec_to_code.py dafny ./specs --mode vibe
  python spec_to_code.py dafny ./specs --mode specvibe --debug
        """,
    )

    parser.add_argument(
        "language",
        type=str,
        choices=list(available_languages.keys()),
        help="Programming language to process",
    )

    parser.add_argument("folder", type=Path, help="Directory with specification files")

    parser.add_argument(
        "--iterations",
        "-i",
        type=int,
        default=5,
        help="Max verification attempts per file (default: 5)",
    )

    parser.add_argument(
        "--debug",
        action="store_true",
        help="Enable debug mode (save intermediate files)",
    )
    
    parser.add_argument(
        "--no-wandb",
        action="store_true", 
        help="Disable Weights & Biases experiment tracking",
    )
    
    parser.add_argument(
        "--delete-after-upload",
        action="store_true",
        help="Delete local generated files after uploading to wandb (requires wandb to be enabled)",
    )

    parser.add_argument(
        "--workers",
        "-w",
        type=int,
        default=4,
        help="Number of parallel workers (default: 4)",
    )

    parser.add_argument(
        "--api-rate-limit-delay",
        type=int,
        default=1,
        help="Delay between API calls in seconds (default: 1)",
    )

    parser.add_argument(
        "--max-directory-traversal-depth",
        type=int,
        default=50,
        help="Maximum depth for directory traversal (default: 50)",
    )

    parser.add_argument(
        "--llm-provider",
        type=str,
        choices=["claude", "gpt", "o1", "gemini", "grok", "deepseek", "glm", "mistral", "openrouter"],
        default="claude",
        help="LLM provider to use. All use OpenRouter with optimized models (default: claude)",
    )

    parser.add_argument(
        "--llm-model",
        type=str,
        help="Specific model to use (defaults to provider's default model)",
    )

    parser.add_argument(
        "--output-folder",
        type=Path,
        help="Parent directory where the implementations folder will be created (defaults to auto-detected src/ directory or current working directory)",
    )

    parser.add_argument(
        "--mode",
        type=str,
        choices=["spec", "vibe", "specvibe"],
        default="spec",
        help="Mode for code generation: 'spec' includes only specification, 'vibe' includes only description, 'specvibe' includes both (default: spec)",
    )

    return parser.parse_args()


def print_startup_info(config):
    """Print startup information and configuration details."""
    from vericoding.core.language_tools import get_tool_path
    
    print(
        f"Starting specification-to-code processing of {config.language_config.name} files (PARALLEL VERSION)..."
    )
    print(f"Directory: {config.files_dir}")
    print(f"Output directory: {config.output_dir}")
    print(f"Tool path: {get_tool_path(config)}")
    print(f"Max iterations: {config.max_iterations}")
    print(f"Parallel workers: {config.max_workers}")
    print(f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")

    if config.debug_mode:
        print(
            "DEBUG MODE: Saves code after each iteration to debug/ subdirectory for analysis."
        )
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")
