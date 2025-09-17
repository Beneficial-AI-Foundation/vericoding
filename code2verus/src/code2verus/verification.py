"""Verus verification functionality for code2verus"""

import asyncio
import os
import tempfile
import logfire
from typing import Tuple


from code2verus.config import cfg
from code2verus.utils import yaml_to_verus


async def verify_verus_code(
    verus_code: str,
    is_yaml: bool = False,
    original_filename: str | None = None,
    benchmark_name: str | None = None,
    benchmark_path: str = "",
) -> Tuple[bool, str, str]:
    """Async function to verify Verus code"""
    src = yaml_to_verus(verus_code) if is_yaml else verus_code
    if is_yaml:
        logfire.info(f"Converted YAML to Verus code ({len(src)} characters)")
    else:
        logfire.info(f"Using raw Verus code ({len(src)} characters)")
    logfire.info(
        f"Verifying Verus code:\n{src[: min(500, len(src))]}...\n"
    )  # Log first 500 characters

    # Create a temporary file for verification (don't save permanent files during verification)
    verification_file = None
    with tempfile.NamedTemporaryFile(mode="w", suffix=".rs", delete=False) as tmpfile:
        tmpfile.write(src)
        verification_file = tmpfile.name
        logfire.info(f"Created temporary file: {verification_file}")

    try:
        # Run verus verification in a separate process
        process = await asyncio.create_subprocess_exec(
            cfg["verus_path"],
            verification_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )

        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=30.0)
            verification_success = process.returncode == 0
            verification_output = stdout.decode("utf-8") if stdout else ""
            verification_error = stderr.decode("utf-8") if stderr else ""
        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            verification_success = False
            verification_output = ""
            verification_error = "Verus verification timed out after 30 seconds"

    except OSError as exc:
        verification_success = False
        verification_output = ""
        verification_error = f"Error running Verus: {str(exc)}"

    finally:
        # Clean up temporary file
        if verification_file:
            try:
                os.unlink(verification_file)
            except OSError:
                pass

    return verification_success, verification_output, verification_error
