import subprocess
import tempfile
import os
from typing import Annotated

from pydantic import Field

from code2verus.config import cfg
from code2verus.models import VerusToolResult, DafnyToolResult


def verus_tool(
    code: Annotated[str, Field(description="Verus code to verify")],
) -> VerusToolResult:
    """Execute Verus verification on the provided code"""
    verus_path = cfg["verus_path"]

    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(mode="w", suffix=".rs", delete=False) as tmpfile:
        tmpfile.write(code)
        temp_file = tmpfile.name

    try:
        # Run verus verification
        result = subprocess.run(
            [verus_path, temp_file], capture_output=True, text=True, timeout=30
        )

        return VerusToolResult(
            success=result.returncode == 0, output=result.stdout, error=result.stderr
        )
    except subprocess.TimeoutExpired:
        return VerusToolResult(
            success=False,
            output="",
            error="Verus verification timed out after 30 seconds",
        )
    except OSError as exc:
        return VerusToolResult(
            success=False, output="", error=f"Error running Verus: {str(exc)}"
        )
    finally:
        # Clean up temporary file
        try:
            os.unlink(temp_file)
        except OSError:
            pass


def dafny_tool(
    code: Annotated[str, Field(description="Dafny code to verify")],
) -> DafnyToolResult:
    """Execute Dafny verification on the provided code"""
    dafny_path = cfg["dafny_path"]

    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", delete=False) as tmpfile:
        tmpfile.write(code)
        temp_file = tmpfile.name

    try:
        # Run dafny verification
        result = subprocess.run(
            [dafny_path, "verify", temp_file],
            capture_output=True,
            text=True,
            timeout=30,
        )

        return DafnyToolResult(
            success=result.returncode == 0, output=result.stdout, error=result.stderr
        )
    except subprocess.TimeoutExpired:
        return DafnyToolResult(
            success=False,
            output="",
            error="Dafny verification timed out after 30 seconds",
        )
    except OSError as exc:
        return DafnyToolResult(
            success=False, output="", error=f"Error running Dafny: {str(exc)}"
        )
    finally:
        # Clean up temporary file
        try:
            os.unlink(temp_file)
        except OSError:
            pass
