"""Language-specific tool handling and verification."""

import os
import shutil
import subprocess
import shlex
import logging
from dataclasses import dataclass
from pathlib import Path

from .config import ProcessingConfig
from vericoding.utils.git_utils import get_repo_root

logger = logging.getLogger(__name__)


@dataclass
class ToolAvailabilityResult:
    """Result of checking tool availability."""

    available: bool
    message: str


@dataclass
class VerificationResult:
    """Result of file verification."""

    success: bool
    output: str
    error: str | None


def get_tool_path(config: ProcessingConfig) -> str:
    """Get the tool path for the current language."""
    # First, try to find the tool in the system PATH
    tool_name = config.language_config.default_tool_path
    system_tool_path = shutil.which(tool_name)

    if system_tool_path:
        return system_tool_path

    # If not found in PATH, fall back to environment variable or default
    tool_path = os.getenv(
        config.language_config.tool_path_env, config.language_config.default_tool_path
    )
    if tool_path.startswith("~/"):
        tool_path = str(Path(tool_path).expanduser())
    return tool_path


def check_tool_availability(config: ProcessingConfig) -> ToolAvailabilityResult:
    """Check if the language tool is available at the specified path."""
    tool_path = get_tool_path(config)
    try:
        # Check if the tool executable exists
        if not Path(tool_path).is_file():
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable not found at: {tool_path}",
            )

        # Check if the file is executable
        if not os.access(tool_path, os.X_OK):
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable is not executable: {tool_path}",
            )

        # Try to run tool with --help to verify it works
        result = subprocess.run(
            [tool_path, "--help"], capture_output=True, text=True, timeout=10
        )

        if result.returncode != 0 and config.language != "lean":
            # Lean might not have --help, so we skip this check for Lean
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable failed to run: {result.stderr}",
            )

        return ToolAvailabilityResult(
            True, f"{config.language_config.name} is available and working"
        )

    except subprocess.TimeoutExpired:
        return ToolAvailabilityResult(
            False,
            f"{config.language_config.name} executable timed out when checking availability",
        )
    except Exception as e:
        return ToolAvailabilityResult(
            False,
            f"Error checking {config.language_config.name} availability: {str(e)}",
        )


def verify_file(config: ProcessingConfig, file_path: str) -> VerificationResult:
    """Verify a file and return the result."""
    tool_path = get_tool_path(config)
    try:
        # First try compilation check if available
        fallback_to_lean = False
        if config.language_config.compile_check_command:
            cmd = [
                part.format(tool_path=tool_path, file_path=file_path)
                for part in config.language_config.compile_check_command
            ]
            try:
                _cwd = (
                    get_repo_root(Path(config.files_dir))
                    if config.language == "lean"
                    else None
                )
                logger.info(
                    f"    ▶ compile_check cmd: (cwd={_cwd or os.getcwd()}) $ {shlex.join(cmd)}"
                )
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    cwd=_cwd,
                )

                if result.returncode != 0:
                    # Compilation failed
                    full_output = result.stdout + result.stderr
                    # If Lean reports unknown module path, fall back to direct lean check
                    if config.language == "lean" and (
                        "unknown module source path" in full_output
                        or "unknown module" in full_output
                    ):
                        logger.info(
                            "    ℹ️  Lake could not resolve module path; will fall back to `lake env lean`"
                        )
                        fallback_to_lean = True
                    else:
                        return VerificationResult(
                            success=False,
                            output=full_output,
                            error=f"Compilation failed: {full_output}",
                        )
            except subprocess.TimeoutExpired as e:
                timeout_msg = f"⏱️  TIMEOUT: Compilation check timed out after 60 seconds"
                logger.info(f"    {timeout_msg}")
                return VerificationResult(
                    success=False, output=str(e), error=timeout_msg
                )

        # Try verification
        # Try verification (with fallback for Lean tmp dirs)
        if config.language == "lean" and fallback_to_lean:
            cmd = ["lake", "env", "lean", f"{file_path}"]
        else:
            cmd = [
                part.format(tool_path=tool_path, file_path=file_path)
                for part in config.language_config.verify_command
            ]
        timeout_value = getattr(
            config.language_config, "timeout", 120
        )  # Default to 120 seconds if not specified
        _cwd = (
            get_repo_root(Path(config.files_dir))
            if config.language == "lean"
            else None
        )
        logger.info(
            f"    ▶ verify cmd: (cwd={_cwd or os.getcwd()}) $ {shlex.join(cmd)} [timeout={timeout_value}s]"
        )
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout_value,
            cwd=_cwd,
        )
        full_output = result.stdout + result.stderr

        success = result.returncode == 0
        # Treat sorry warnings as failures for Lean unless explicitly bypassed elsewhere
        if config.language == "lean":
            if "warning: declaration uses 'sorry'" in full_output:
                logger.info("    ⚠️  Lean 'sorry' warnings detected; marking as failure")
                success = False

        if success:
            return VerificationResult(success=True, output=full_output, error=None)
        else:
            return VerificationResult(
                success=False,
                output=full_output,
                error=f"Verification failed: {full_output}",
            )

    except subprocess.TimeoutExpired as e:
        timeout_msg = f"⏱️  TIMEOUT: Verification timed out after {timeout_value} seconds"
        logger.info(f"    {timeout_msg}")
        return VerificationResult(
            success=False, output=str(e), error=timeout_msg
        )
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))


def find_spec_files(config: ProcessingConfig) -> list[str]:
    """Find specification files for the current language.

    For Lean, skip generated/debug folders to avoid re-processing outputs:
    - Any directory named exactly "_gen" or ending with "_gen"
    - Any directory starting with "Run_" or named "debug"
    - The sibling library folder "dafnybench_gen"
    - Common junk: ".git", ".lake", "__pycache__", "wandb"
    """
    try:
        files: list[str] = []

        def should_skip_dir(dir_name: str) -> bool:
            name = dir_name
            if name in {".git", ".lake", "__pycache__", "debug", "wandb"}:
                return True
            if name == "_gen" or name.endswith("_gen"):
                return True
            if name.startswith("Run_"):
                return True
            if name == "dafnybench_gen":
                return True
            return False

        for root, dirs, filenames in os.walk(config.files_dir):
            # Prune directories in-place for efficiency
            dirs[:] = [d for d in dirs if not should_skip_dir(d)]
            for f in filenames:
                if not f.endswith(config.language_config.file_extension):
                    continue
                file_path = str(Path(root) / f)
                if config.language == "lean":
                    # Only process files that contain 'sorry'
                    try:
                        with Path(file_path).open() as file:
                            for line in file:
                                if "sorry" in line:
                                    files.append(file_path)
                                    break
                    except Exception:
                        # Ignore unreadable files
                        continue
                else:
                    files.append(file_path)
        return files
    except Exception as e:
        print(f"Error reading directory {config.files_dir}: {e}")
        return []
