"""Agent creation and translation logic for code2verus"""

from pydantic_ai import Agent
import logfire
import yaml

from code2verus.config import (
    system_prompt,
    cfg,
    full_cfg,
    get_config_value,
    get_error_template,
)
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
    max_iterations: int | None = None,
) -> tuple[str, int, str]:
    """Translate source code to Verus using the agent with verification feedback"""
    # Use config value if max_iterations not provided
    if max_iterations is None:
        max_iterations = get_config_value("max_translation_iterations")

    agent = create_agent(source_language)

    # Initialize variables
    result = None
    output_content = ""
    rust_for_verification = ""
    iteration = 0

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
                yaml.safe_load(yaml_content)
                logfire.info("YAML validation successful")
            except yaml.YAMLError as e:
                logfire.warning(f"Generated YAML is malformed: {e}")
                if iteration < max_iterations - 1:
                    # If we have more iterations, prepare feedback to fix the YAML
                    yaml_error_feedback = get_error_template(
                        "yaml_syntax_error",
                        error=str(e),
                        source_language=source_language,
                        source_language_lower=source_language.lower(),
                        source_code=source_code,
                        additional_prompt=additional_prompt,
                    )
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
                feedback_prompt = get_error_template(
                    "verification_error",
                    verification_error=verification_error,
                    verification_output=verification_output,
                    source_language=source_language,
                    source_language_lower=source_language.lower(),
                    source_code=source_code,
                    additional_prompt=additional_prompt,
                )
                user_prompt = feedback_prompt

    # Return the actual number of iterations performed
    num_iterations = iteration + 1

    return output_content, num_iterations, rust_for_verification
