"""Agent creation and translation logic for code2verus"""

from pydantic_ai import Agent
import logfire

from code2verus.config import system_prompt, cfg, full_cfg
from code2verus.tools import verus_tool, dafny_tool
from code2verus.utils import extract_rust_code, concatenate_yaml_fields


def create_agent(source_language: str = "dafny"):
    """Create and return a configured PydanticAI agent with tools"""
    # Load language-specific system prompt
    language_prompt = full_cfg.get("system_prompts", {}).get(
        source_language.lower(), system_prompt
    )

    return Agent(
        cfg["model"],
        name="code2verus",
        deps_type=str,
        output_type=str,
        tools=[verus_tool, dafny_tool],
        system_prompt=language_prompt,
        retries=10,
    )


async def translate_code_to_verus(
    source_code: str,
    source_language: str = "dafny",
    is_yaml: bool = False,
    max_iterations: int = None,
) -> tuple[str, int, str]:
    """Translate source code to Verus using the agent with verification feedback"""
    # Use config value if max_iterations not provided, with fallback to 3
    if max_iterations is None:
        max_iterations = cfg.get("max_translation_iterations", 3)
    
    agent = create_agent(source_language)

    # Get language-specific prompts from config
    if is_yaml:
        yaml_instructions = full_cfg.get("yaml_instructions", {})
        logfire.info(
            f"Available yaml_instructions keys: {list(yaml_instructions.keys())}"
        )

        additional_prompt = yaml_instructions.get(source_language.lower(), "")
        logfire.info(
            f"YAML mode for {source_language}, additional_prompt length: {len(additional_prompt)}"
        )
        logfire.debug(
            f"First 200 chars of additional_prompt: {additional_prompt[:200]}..."
        )
    else:
        additional_prompt = full_cfg.get("default_prompts", {}).get(
            source_language.lower(), ""
        )
        logfire.info(
            f"Non-YAML mode for {source_language}, additional_prompt length: {len(additional_prompt)}"
        )

    user_prompt = f"""
Please translate the following {source_language} code to Verus:

```{source_language.lower()}
{source_code}
```

{additional_prompt}
"""

    # Iterative improvement with verification feedback
    for iteration in range(max_iterations):
        logfire.info(f"Translation iteration {iteration + 1}/{max_iterations}")

        result = await agent.run(user_prompt, deps=source_code)

        # Handle output based on file type
        if is_yaml:
            # For YAML files, use the raw output directly (no extraction needed)
            yaml_content = result.output.strip()
            logfire.info(f"YAML output length: {len(yaml_content)}")
            logfire.debug(f"YAML output starts with: {yaml_content[:100]}...")

            # Validate YAML syntax before proceeding
            try:
                import yaml

                yaml.safe_load(yaml_content)
                logfire.info("YAML validation successful")
            except yaml.YAMLError as e:
                logfire.warning(f"Generated YAML is malformed: {e}")
                if iteration < max_iterations - 1:
                    # If we have more iterations, prepare feedback to fix the YAML
                    yaml_error_feedback = f"""
The generated YAML has syntax errors: {e}

Please fix the YAML syntax issues and generate valid YAML. Common issues:
- Make sure field names end with colons (:)
- Check indentation (use spaces, not tabs)
- Ensure all string values containing special characters are properly quoted
- Use the |- syntax for multi-line strings

Here's the original {source_language} code again:

```{source_language.lower()}
{source_code}
```

{additional_prompt}
"""
                    user_prompt = yaml_error_feedback
                    continue  # Skip verification and go to next iteration to fix YAML

            # Also generate concatenated Rust code from YAML for verification
            rust_content = concatenate_yaml_fields(yaml_content)
            logfire.info(f"Concatenated Rust code length: {len(rust_content)}")

            # Return YAML content as main output, Rust content as secondary
            output_content = yaml_content
            rust_for_verification = rust_content
        else:
            # For regular files, extract code from markdown blocks
            output_content = extract_rust_code(result.output)
            rust_for_verification = output_content  # Same content for both

        # Verify the generated code (except on the last iteration if we want to return regardless)
        if iteration < max_iterations - 1:
            # Import here to avoid circular imports
            from code2verus.verification import verify_verus_code

            (
                verification_success,
                verification_output,
                verification_error,
            ) = await verify_verus_code(rust_for_verification, is_yaml)

            if verification_success:
                logfire.info(f"Verification successful on iteration {iteration + 1}")
                break
            else:
                logfire.info(
                    f"Verification failed on iteration {iteration + 1}, trying to improve..."
                )
                # Prepare feedback for next iteration with specific error details
                feedback_prompt = f"""
The previous translation failed verification. Here are the specific errors:

Verification Error: {verification_error}

Verification Output: {verification_output}

Please fix the Verus code to address these verification errors. Pay special attention to:
- Syntax errors (missing semicolons, incorrect brackets, etc.)
- Type mismatches
- Incorrect function signatures
- Missing imports or module declarations

Here's the original {source_language} code again:

```{source_language.lower()}
{source_code}
```

{additional_prompt}
"""
                user_prompt = feedback_prompt

    # Calculate total iterations based on all messages exchanged
    num_iterations = len(result.all_messages()) // 3

    return output_content, num_iterations, rust_for_verification
