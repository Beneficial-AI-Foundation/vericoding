"""Verus verification functionality for code2verus"""
import asyncio
import os
import tempfile

from code2verus.config import cfg


async def verify_verus_code(verus_code: str) -> tuple[bool, str, str]:
    """Async function to verify Verus code"""
    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".rs", delete=False
    ) as tmpfile:
        tmpfile.write(verus_code)
        temp_file = tmpfile.name

    try:
        # Run verus verification in a separate process
        process = await asyncio.create_subprocess_exec(
            cfg["verus_path"], temp_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        
        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=30.0)
            verification_success = process.returncode == 0
            verification_output = stdout.decode('utf-8') if stdout else ""
            verification_error = stderr.decode('utf-8') if stderr else ""
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
        try:
            os.unlink(temp_file)
        except OSError:
            pass

    return verification_success, verification_output, verification_error
