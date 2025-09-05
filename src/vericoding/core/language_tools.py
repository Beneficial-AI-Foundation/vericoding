"""Language-specific tool handling and verification."""

import os
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .config import ProcessingConfig


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
        if config.language_config.compile_check_command:
            cmd = [
                part.format(tool_path=tool_path, file_path=file_path)
                for part in config.language_config.compile_check_command
            ]
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

                if result.returncode != 0:
                    # Compilation failed
                    full_output = result.stdout + result.stderr
                    return VerificationResult(
                        success=False,
                        output=full_output,
                        error=f"Compilation failed: {full_output}",
                    )
            except subprocess.TimeoutExpired as e:
                timeout_msg = f"⏱️  TIMEOUT: Compilation check timed out after 60 seconds"
                print(f"    {timeout_msg}")
                return VerificationResult(
                    success=False, output=str(e), error=timeout_msg
                )

        # Try verification
        cmd = [
            part.format(tool_path=tool_path, file_path=file_path)
            for part in config.language_config.verify_command
        ]
        timeout_value = getattr(
            config.language_config, "timeout", 120
        )  # Default to 120 seconds if not specified
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_value
        )
        full_output = result.stdout + result.stderr

        success = result.returncode == 0
        # Treat sorry warnings as failures for Lean unless explicitly bypassed elsewhere
        if config.language == "lean":
            if "warning: declaration uses 'sorry'" in full_output:
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
        print(f"    {timeout_msg}")
        return VerificationResult(
            success=False, output=str(e), error=timeout_msg
        )
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))


def find_spec_files(config: ProcessingConfig) -> list[str]:
    """Find specification files for the current language."""
    try:
        files = []
        for root, _dirs, filenames in os.walk(config.files_dir):
            for f in filenames:
                if f.endswith(config.language_config.file_extension):
                    file_path = str(Path(root) / f)
                    # For Lean, check if file contains 'sorry'
                    if config.language == "lean":
                        with Path(file_path).open() as file:
                            for line in file:
                                if "sorry" in line:
                                    files.append(file_path)
                                    break
                    else:
                        files.append(file_path)
        return files
    except Exception as e:
        print(f"Error reading directory {config.files_dir}: {e}")
        return []
