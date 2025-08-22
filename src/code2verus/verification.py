"""Verus verification functionality for code2verus"""
import asyncio
import os
import tempfile
import yaml

from code2verus.config import cfg

def yaml_to_verus(verus_yaml: str) -> str:     
    try:
        has_verus = "verus!" in verus_yaml
        # Remove prelude and main if present so we can ensure they always appear first and last
        cleaned = verus_yaml.replace("use vstd::prelude::*;", "").replace("fn main() {}", "")
        as_yaml = yaml.safe_load(cleaned)
        prefix = f"use vstd::prelude::*;\n{"" if has_verus else "verus! {"}"
        suffix = f"fn main() {{}}\n{"" if has_verus else "}"}"
        return  f"{prefix}\n{as_yaml['vc-preamble']}\n{as_yaml['vc-helpers']}\n{as_yaml['vc-spec']}\n{as_yaml['vc-code']}\n{as_yaml['vc-postamble']}\n{suffix}\n"""
    except:
        return verus_yaml

async def verify_verus_code(verus_code: str, is_yaml: bool = False ) -> tuple[bool, str, str]:
    """Async function to verify Verus code"""
    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".rs", delete=False
    ) as tmpfile:
        src = yaml_to_verus(verus_code) if is_yaml else verus_code
        tmpfile.write(src)
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
