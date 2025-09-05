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
        if 'vc-preamble' in as_yaml and as_yaml['vc-preamble']:
            parts.append(as_yaml['vc-preamble'])
        
        if 'vc-helpers' in as_yaml and as_yaml['vc-helpers']:
            parts.append(as_yaml['vc-helpers'])
        
        if 'vc-signature' in as_yaml and as_yaml['vc-signature']:
            parts.append(as_yaml['vc-signature'])
        
        if 'vc-implementation' in as_yaml and as_yaml['vc-implementation']:
            parts.append(as_yaml['vc-implementation'])
        
        if 'vc-condition' in as_yaml and as_yaml['vc-condition']:
            parts.append(as_yaml['vc-condition'])
        
        if 'vc-proof' in as_yaml and as_yaml['vc-proof']:
            parts.append(as_yaml['vc-proof'])
        
        if 'vc-postamble' in as_yaml and as_yaml['vc-postamble']:
            parts.append(as_yaml['vc-postamble'])
        
        return '\n'.join(parts)
        
    except Exception as e:
        logfire.info(f"Failed to parse YAML, using as-is: {e}")
        return verus_yaml

async def verify_verus_code(verus_code: str, is_yaml: bool = False ) -> tuple[bool, str, str]:
    """Async function to verify Verus code"""
    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".rs", delete=False
    ) as tmpfile:
        src = yaml_to_verus(verus_code) if is_yaml else verus_code
        if is_yaml:
            logfire.info(f"Converted YAML to Verus code ({len(src)} characters)")
        else:
            logfire.info(f"Using raw Verus code ({len(src)} characters)")
        logfire.info(f"Verifying Verus code:\n{src[:500]}...\n")  # Log first 500 characters
        tmpfile.write(src)
        temp_file = tmpfile.name
        logfire.info(f"Created temporary file: {temp_file}")

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
    #finally:
        # Clean up temporary file
    #    try:
    #        os.unlink(temp_file)
    #    except OSError:
    #        pass

    return verification_success, verification_output, verification_error
