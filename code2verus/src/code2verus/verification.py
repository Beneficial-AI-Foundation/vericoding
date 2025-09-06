"""Verus verification functionality for code2verus"""

import asyncio
import os
import tempfile
import yaml
import logfire


from code2verus.config import cfg


def yaml_to_verus(verus_yaml: str) -> str:
    try:
        as_yaml = yaml.safe_load(verus_yaml)

        # Handle the actual YAML structure from the verina benchmark
        parts = []

        # Add each section if it exists
        if "vc-description" in as_yaml and as_yaml["vc-description"]:
            parts.append(as_yaml["vc-description"])

        if "vc-preamble" in as_yaml and as_yaml["vc-preamble"]:
            parts.append(as_yaml["vc-preamble"])

        if "vc-helpers" in as_yaml and as_yaml["vc-helpers"]:
            parts.append(as_yaml["vc-helpers"])

        if "vc-signature" in as_yaml and as_yaml["vc-signature"]:
            parts.append(as_yaml["vc-signature"])

        if "vc-implementation" in as_yaml and as_yaml["vc-implementation"]:
            parts.append(as_yaml["vc-implementation"])

        if "vc-condition" in as_yaml and as_yaml["vc-condition"]:
            parts.append(as_yaml["vc-condition"])

        if "vc-proof" in as_yaml and as_yaml["vc-proof"]:
            parts.append(as_yaml["vc-proof"])

        if "vc-postamble" in as_yaml and as_yaml["vc-postamble"]:
            parts.append(as_yaml["vc-postamble"])

        return "\n".join(parts)

    except Exception as e:
        logfire.info(f"Failed to parse YAML, using as-is: {e}")
        return verus_yaml


async def verify_verus_code(
    verus_code: str,
    is_yaml: bool = False,
    original_filename: str = None,
    benchmark_name: str = None,
    benchmark_path: str = "",
) -> tuple[bool, str, str]:
    """Async function to verify Verus code"""
    src = yaml_to_verus(verus_code) if is_yaml else verus_code
    if is_yaml:
        logfire.info(f"Converted YAML to Verus code ({len(src)} characters)")
    else:
        logfire.info(f"Using raw Verus code ({len(src)} characters)")
    logfire.info(f"Verifying Verus code:\n{src[:500]}...\n")  # Log first 500 characters

    # Save the Verus code to the files folder if we have the necessary information
    verification_file = None
    if original_filename and benchmark_name and is_yaml:
        try:
            from pathlib import Path
            from code2verus.config import ARTIFACTS

            # Use the new path derivation logic if available
            if benchmark_path:
                from code2verus.processing import derive_output_path

                files_folder = derive_output_path(benchmark_path, benchmark_name, False)
            else:
                # Fallback to old behavior
                files_folder = ARTIFACTS / benchmark_name / "files"

            files_folder.mkdir(parents=True, exist_ok=True)

            # Create the corresponding .rs filename from the original YAML filename
            original_path = Path(original_filename)
            verus_filename = original_path.with_suffix(".rs").name
            verus_file_path = files_folder / verus_filename

            # Save the converted Verus code
            with open(verus_file_path, "w") as f:
                f.write(src)
            logfire.info(f"Saved Verus file to: {verus_file_path}")
            verification_file = str(verus_file_path)
        except Exception as e:
            logfire.info(f"Failed to save Verus file: {e}")

    # If we couldn't save to files folder, create a temporary file as fallback
    if verification_file is None:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".rs", delete=False
        ) as tmpfile:
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

    # Clean up temporary file only if we created one (not for saved files)
    if verification_file and original_filename is None:
        try:
            os.unlink(verification_file)
        except OSError:
            pass

    return verification_success, verification_output, verification_error
