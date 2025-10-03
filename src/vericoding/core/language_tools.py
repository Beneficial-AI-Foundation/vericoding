"""Language-specific tool handling and verification."""

import os
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

from .config import ProcessingConfig
import logging


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


def file_path_to_lean_module(file_path: str) -> str:
    """Convert a file path to a Lean module name.

    Examples:
        benchmarks/lean/test/file.lean -> Benchmarks.test.file
        benchmarks/lean/verina/basic.lean -> Benchmarks.verina.basic
        benchmarks/lean/vericoder_xxx/test/file.lean -> Benchmarks.test.file
        lean/Generated/MyModule.lean -> Generated.MyModule
    """
    path = Path(file_path)

    # Remove the .lean extension
    parts = list(path.parts)
    parts[-1] = path.stem

    # Find the library root (benchmarks/lean or lean)
    if "benchmarks" in parts and "lean" in parts:
        # Find the index of "lean"
        lean_idx = parts.index("lean")
        # Take everything after "benchmarks/lean"
        subpath_parts = parts[lean_idx + 1 :]

        # HARDCODED: Filter out vericoder_* directories (they're not part of the module path)
        filtered_parts = [p for p in subpath_parts if not p.startswith("vericoder_")]

        # Prepend "Benchmarks" as the library name
        module_parts = ["Benchmarks"] + filtered_parts
    elif "lean" in parts:
        # For files in lean/ directory (like lean/Generated/...)
        lean_idx = parts.index("lean")
        module_parts = parts[lean_idx + 1 :]
    else:
        # Fallback: just use the parts as-is
        module_parts = parts

    return ".".join(module_parts)


def verify_file(config: ProcessingConfig, file_path: str) -> VerificationResult:
    """Verify a file and return the result."""
    tool_path = get_tool_path(config)

    # For Lean, we need special handling because generated files in vericoder_*
    # directories need to be copied to the registered library directories
    temp_file_for_lean = None
    path_to_use = file_path

    if config.language == "lean":
        file_obj = Path(file_path)

        # Check if this is a generated file (in output directory, not in benchmarks/lean)
        # by checking if path contains vericoder_*
        if any(part.startswith("vericoder_") for part in file_obj.parts):
            # This is a generated file - copy it to benchmarks/lean for verification
            # Read the file content
            try:
                with open(file_path, "r") as f:
                    content = f.read()

                # Create a temp file in benchmarks/lean with _temp suffix
                # Extract the relative path structure (skip vericoder_* dir but keep subdirs)
                parts = list(file_obj.parts)
                vericoder_idx = next(
                    i for i, p in enumerate(parts) if p.startswith("vericoder_")
                )
                # Take parts after vericoder_* (includes subdirectories like 'test/files/')
                relative_parts = parts[vericoder_idx + 1 :]

                # Rebuild the path: benchmarks/lean/<subdirs>/filename_temp.lean
                if len(relative_parts) > 1:
                    # Has subdirectories - preserve them
                    subdirs = relative_parts[:-1]  # All but the filename
                    filename = relative_parts[-1]  # Just the filename
                    temp_path = (
                        Path("benchmarks/lean")
                        / Path(*subdirs)
                        / f"{Path(filename).stem}_temp{Path(filename).suffix}"
                    )
                else:
                    # No subdirectories - file directly in vericoder_* root
                    filename = relative_parts[0]
                    temp_path = (
                        Path("benchmarks/lean")
                        / f"{Path(filename).stem}_temp{Path(filename).suffix}"
                    )

                temp_path.parent.mkdir(parents=True, exist_ok=True)

                with open(temp_path, "w") as f:
                    f.write(content)

                temp_file_for_lean = temp_path
                # Use the temp file path directly - lake build expects file paths, not module names!
                path_to_use = str(temp_path)
            except Exception as e:
                return VerificationResult(
                    success=False,
                    output="",
                    error=f"Failed to create temp file for Lean verification: {e}",
                )
        # else: Original spec file - use the file path as-is (lake build expects file paths)

    try:
        # First try compilation check if available
        if config.language_config.compile_check_command:
            cmd = [
                part.format(tool_path=tool_path, file_path=path_to_use)
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
                timeout_msg = "⏱️  TIMEOUT: Compilation check timed out after 60 seconds"
                print(f"    {timeout_msg}")
                return VerificationResult(
                    success=False, output=str(e), error=timeout_msg
                )

        # Try verification
        cmd = [
            part.format(tool_path=tool_path, file_path=path_to_use)
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

    except subprocess.TimeoutExpired as e:
        timeout_msg = (
            f"⏱️  TIMEOUT: Verification timed out after {timeout_value} seconds"
        )
        print(f"    {timeout_msg}")
        return VerificationResult(success=False, output=str(e), error=timeout_msg)
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))
    finally:
        # Clean up temp file if we created one for Lean
        if temp_file_for_lean and temp_file_for_lean.exists():
            try:
                temp_file_for_lean.unlink()
            except (FileNotFoundError, PermissionError) as e:
                # File already deleted or permission issue - not critical
                logging.debug(f"Could not clean up temp file {temp_file_for_lean}: {e}")
            except OSError as e:
                # Other OS errors during cleanup
                logging.warning(
                    f"Failed to clean up temp file {temp_file_for_lean}: {e}"
                )


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
        # Sort for deterministic ordering across runs
        files.sort()
        return files
    except Exception as e:
        print(f"Error reading directory {config.files_dir}: {e}")
        return []
