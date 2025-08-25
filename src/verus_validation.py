#!/usr/bin/env python3
"""
Shared Verus validation functionality.

This module provides common functions for validating Rust code with Verus,
converting YAML to Rust, and manipulating YAML helper sections.
"""

import subprocess
import tempfile
import shutil
from pathlib import Path
from typing import Tuple


class VerusNotFoundError(Exception):
    """Raised when Verus executable is required but not found."""
    pass


def find_verus_executable() -> str:
    """
    Find the verus executable in PATH or common locations.
    
    Returns:
        str: Path to the verus executable
        
    Raises:
        VerusNotFoundError: If Verus executable is not found
    """
    # Check if verus is in PATH
    if shutil.which("verus"):
        return "verus"
    
    # Check common installation locations
    common_paths = [
        "/usr/local/bin/verus",
        "/usr/bin/verus", 
        Path.home() / ".cargo/bin/verus",
        Path.home() / "bin/verus"
    ]
    
    for path in common_paths:
        if Path(path).exists():
            return str(path)
    
    raise VerusNotFoundError(
        "Verus executable not found. Please install verus or add it to PATH.\n"
        "Try: cargo install --git https://github.com/verus-lang/verus verus"
    )


def verify_rust_with_verus(rust_path: Path, verus_cmd: str) -> Tuple[bool, str]:
    """
    Run verus --no-verify on the Rust file and return success status and output.
    
    Args:
        rust_path: Path to the Rust file to verify
        verus_cmd: Path to the verus executable
        
    Returns:
        Tuple[bool, str]: (success, output_message)
    """
    try:
        result = subprocess.run([
            verus_cmd, "--no-verify", str(rust_path)
        ], capture_output=True, text=True, timeout=30)
        
        success = result.returncode == 0
        output = f"stdout: {result.stdout}\nstderr: {result.stderr}" if result.stdout or result.stderr else "No output"
        
        return success, output
        
    except subprocess.TimeoutExpired:
        return False, "Verus timed out after 30 seconds"
    except Exception as e:
        return False, f"Error running verus: {e}"


def create_yaml_without_helpers(yaml_content: str) -> str:
    """
    Create a modified YAML with empty vc-helpers section.
    
    Args:
        yaml_content: Original YAML content
        
    Returns:
        str: Modified YAML content with empty vc-helpers section
    """
    lines = yaml_content.split('\n')
    result_lines = []
    in_helpers = False
    
    for line in lines:
        if line.startswith('vc-helpers:'):
            result_lines.append(line)
            result_lines.append('')  # Empty helpers section
            in_helpers = True
        elif line.startswith('vc-spec:') and in_helpers:
            # End of helpers section, start of spec section
            result_lines.append(line)
            in_helpers = False
        elif not in_helpers:
            result_lines.append(line)
        # Skip lines that are part of vc-helpers content
    
    return '\n'.join(result_lines)


def convert_yaml_to_rust(yaml_path: Path, temp_dir: Path) -> Tuple[bool, Path]:
    """
    Convert YAML file to Rust using convert_from_yaml.py, output to temp directory.
    
    Args:
        yaml_path: Path to the YAML file to convert
        temp_dir: Temporary directory for output
        
    Returns:
        Tuple[bool, Path]: (success, path_to_rust_file)
    """
    try:
        # Create a copy of the YAML file in temp directory to avoid modifying tests dir
        temp_yaml = temp_dir / yaml_path.name
        if temp_yaml != yaml_path:  # Only copy if different paths
            shutil.copy2(yaml_path, temp_yaml)
        else:
            temp_yaml = yaml_path
        
        # Find the project root to run the conversion script
        current_file = Path(__file__)
        project_root = current_file.parent.parent
        
        result = subprocess.run([
            "uv", "run", "src/convert_from_yaml.py",
            str(temp_yaml),
            "--suffix", "rs"
        ], capture_output=True, text=True, cwd=project_root)
        
        if result.returncode != 0:
            return False, Path()
            
        # The convert script creates the .rs file next to the yaml file
        temp_rust = temp_yaml.with_suffix('.rs')
        return temp_rust.exists(), temp_rust
        
    except Exception as e:
        return False, Path()


def validate_yaml_with_verus(yaml_content: str, verus_cmd: str, temp_dir: Path) -> Tuple[bool, bool, str]:
    """
    Validate YAML by converting to Rust and checking with Verus.
    
    Args:
        yaml_content: YAML content to validate
        verus_cmd: Path to the verus executable
        temp_dir: Temporary directory for intermediate files
        
    Returns:
        Tuple[bool, bool, str]: (original_valid, no_helpers_valid, error_message)
    """
    import uuid
    
    try:
        # Test original YAML
        temp_yaml = temp_dir / f"temp_{uuid.uuid4().hex[:8]}.yaml"
        with open(temp_yaml, 'w', encoding='utf-8') as f:
            f.write(yaml_content)
        
        success, rust_file = convert_yaml_to_rust(temp_yaml, temp_dir)
        if not success:
            return False, False, "YAML to Rust conversion failed"
        
        original_valid, original_msg = verify_rust_with_verus(rust_file, verus_cmd)
        
        if not original_valid:
            return False, False, f"Original failed: {original_msg}"
        
        # Test version without helpers (if applicable)
        if 'vc-helpers: |-' not in yaml_content:
            # No helpers to remove, consider it valid
            return True, True, "No helpers to remove"
        
        # Create version without helpers
        no_helpers_yaml = create_yaml_without_helpers(yaml_content)
        temp_yaml_no_helpers = temp_dir / f"temp_no_helpers_{uuid.uuid4().hex[:8]}.yaml"
        with open(temp_yaml_no_helpers, 'w', encoding='utf-8') as f:
            f.write(no_helpers_yaml)
        
        success_no_helpers, rust_file_no_helpers = convert_yaml_to_rust(temp_yaml_no_helpers, temp_dir)
        if not success_no_helpers:
            return True, False, "No-helpers YAML to Rust conversion failed"
        
        no_helpers_valid, no_helpers_msg = verify_rust_with_verus(rust_file_no_helpers, verus_cmd)
        
        return original_valid, no_helpers_valid, no_helpers_msg if not no_helpers_valid else "Success"
        
    except Exception as e:
        return False, False, f"Validation error: {e}"