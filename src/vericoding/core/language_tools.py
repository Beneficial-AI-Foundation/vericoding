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


def check_tool_availability(config: ProcessingConfig) -> None:
    """Check if the language tool is available and exit on failure."""
    import sys
    
    def _exit_with_error(message: str):
        """Helper to print error and exit."""
        tool_path = get_tool_path(config)
        print(f"Error: {message}")
        print(f"Please ensure {config.language_config.name} is installed and {config.language_config.tool_path_env} is set correctly.")
        print(f"Current {config.language_config.tool_path_env}: {tool_path}")
        print(f"You can set it with: export {config.language_config.tool_path_env}=/path/to/{config.language}")
        sys.exit(1)
    
    tool_path = get_tool_path(config)
    print(f"Checking {config.language_config.name} availability...")
    
    try:
        # Check if tool exists, is executable, and works
        if (not Path(tool_path).is_file() or 
            not os.access(tool_path, os.X_OK) or 
            (config.language != "lean" and 
             subprocess.run([tool_path, "--help"], capture_output=True, text=True, timeout=10).returncode != 0)):
            _exit_with_error(f"{config.language_config.name} is not available or not working properly")

        print(f"✓ {config.language_config.name} is available and working")
        print("")

    except Exception as e:
        _exit_with_error(f"Error checking {config.language_config.name}: {str(e)}")


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
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            if result.returncode != 0:
                # Compilation failed
                full_output = result.stdout + result.stderr
                return VerificationResult(
                    success=False,
                    output=full_output,
                    error=f"Compilation failed: {full_output}",
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

        if success:
            return VerificationResult(success=True, output=full_output, error=None)
        else:
            return VerificationResult(
                success=False,
                output=full_output,
                error=f"Verification failed: {full_output}",
            )

    except subprocess.TimeoutExpired:
        return VerificationResult(
            success=False, output="", error="Verification timeout"
        )
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))


def find_spec_files(config: ProcessingConfig) -> list[str]:
    """Find YAML specification files for the current language."""
    try:
        files = []
        for root, _dirs, filenames in os.walk(config.files_dir):
            for f in filenames:
                if f.endswith(('.yaml', '.yml')):
                    file_path = str(Path(root) / f)
                    files.append(file_path)
        return files
    except Exception as e:
        print(f"Error reading directory {config.files_dir}: {e}")
        return []
