"""Code verification functionality for code2verus"""

import asyncio
import os
import tempfile
import logfire
from typing import Tuple


from code2verus.config import cfg
from code2verus.utils import yaml_to_verus, yaml_to_lean


async def verify_code(
    code: str,
    target_language: str = "verus",
    is_yaml: bool = False,
    original_filename: str | None = None,
    benchmark_name: str | None = None,
    benchmark_path: str = "",
) -> Tuple[bool, str, str]:
    """Generic function to verify code in different target languages"""
    if target_language.lower() == "verus":
        return await verify_verus_code(
            code, is_yaml, original_filename, benchmark_name, benchmark_path
        )
    elif target_language.lower() == "dafny":
        return await verify_dafny_code(
            code, is_yaml, original_filename, benchmark_name, benchmark_path
        )
    elif target_language.lower() == "lean":
        return await verify_lean_code(
            code, is_yaml, original_filename, benchmark_name, benchmark_path
        )
    else:
        # For unsupported languages, return success without verification
        logfire.warning(f"Verification not implemented for {target_language}, skipping")
        return True, f"Verification skipped for {target_language}", ""


async def verify_dafny_code(
    dafny_code: str,
    is_yaml: bool = False,
    original_filename: str | None = None,
    benchmark_name: str | None = None,
    benchmark_path: str = "",
) -> Tuple[bool, str, str]:
    """Async function to verify Dafny code"""
    # For YAML, we'd need a yaml_to_dafny function (not implemented yet)
    src = dafny_code  # For now, assume direct Dafny code
    if is_yaml:
        logfire.info("YAML to Dafny conversion not yet implemented, using raw content")

    logfire.info(f"Verifying Dafny code ({len(src)} characters)")
    logfire.info(f"Dafny code preview:\n{src[: min(500, len(src))]}...\n")

    # Create a temporary file for verification
    verification_file = None
    with tempfile.NamedTemporaryFile(mode="w", suffix=".dfy", delete=False) as tmpfile:
        tmpfile.write(src)
        verification_file = tmpfile.name
        logfire.info(f"Created temporary Dafny file: {verification_file}")

    try:
        # Run dafny verification
        process = await asyncio.create_subprocess_exec(
            cfg["dafny_path"],
            "verify",
            verification_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )

        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=30.0)
            verification_success = process.returncode == 0
            verification_output = stdout.decode("utf-8") if stdout else ""
            verification_error = stderr.decode("utf-8") if stderr else ""

            if verification_success:
                logfire.info("Dafny verification successful")
            else:
                logfire.warning(f"Dafny verification failed: {verification_error}")

            return verification_success, verification_output, verification_error

        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            error_msg = "Dafny verification timed out after 30 seconds"
            logfire.error(error_msg)
            return False, "", error_msg

    except Exception as e:
        error_msg = f"Error during Dafny verification: {str(e)}"
        logfire.error(error_msg)
        return False, "", error_msg

    finally:
        # Clean up temporary file
        if verification_file and os.path.exists(verification_file):
            try:
                os.unlink(verification_file)
                logfire.info(f"Cleaned up temporary file: {verification_file}")
            except Exception as e:
                logfire.warning(f"Failed to clean up temporary file: {e}")


async def verify_lean_code(
    lean_code: str,
    is_yaml: bool = False,
    original_filename: str | None = None,
    benchmark_name: str | None = None,
    benchmark_path: str = "",
) -> Tuple[bool, str, str]:
    """Async function to verify Lean code"""
    # Convert YAML to Lean code if needed
    src = yaml_to_lean(lean_code) if is_yaml else lean_code
    if is_yaml:
        logfire.info(f"Converted YAML to Lean code ({len(src)} characters)")

    logfire.info(f"Verifying Lean code with Lake environment ({len(src)} characters)")
    logfire.info(f"Lean code preview:\n{src[: min(500, len(src))]}...\n")

    # Create a temporary file for verification
    verification_file = None
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as tmpfile:
        tmpfile.write(src)
        verification_file = tmpfile.name
        logfire.info(f"Created temporary Lean file: {verification_file}")

    try:
        # Run lean verification using lake env lean
        lake_path = cfg.get("lake_path", "lake")
        process = await asyncio.create_subprocess_exec(
            lake_path,
            "env",
            "lean",
            verification_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )

        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=30.0)
            verification_success = process.returncode == 0
            verification_output = stdout.decode("utf-8") if stdout else ""
            verification_error = stderr.decode("utf-8") if stderr else ""

            if verification_success:
                logfire.info("Lean verification with Lake environment successful")
            else:
                logfire.warning(f"Lean verification failed: {verification_error}")

            return verification_success, verification_output, verification_error

        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            error_msg = "Lean verification timed out after 30 seconds"
            logfire.error(error_msg)
            return False, "", error_msg

    except Exception as e:
        error_msg = f"Error during Lean verification: {str(e)}"
        logfire.error(error_msg)
        return False, "", error_msg

    finally:
        # Clean up temporary file
        if verification_file and os.path.exists(verification_file):
            try:
                os.unlink(verification_file)
                logfire.info(f"Cleaned up temporary file: {verification_file}")
            except Exception as e:
                logfire.warning(f"Failed to clean up temporary file: {e}")


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
