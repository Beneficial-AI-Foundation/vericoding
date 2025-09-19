"""Agent creation and translation logic for code2verus

This module implements an iterative translation approach that reuses a single agent
instance across multiple iterations while maintaining true conversational context
using PydanticAI's message_history parameter.

Key design decisions:
1. Agent reuse: Create one agent instance and reuse it for all iterations
2. True conversation context: Use message_history parameter to maintain conversation
   state across iterations, rather than manually building context in prompts
3. Structured message history: Track conversation using proper PydanticAI message objects
"""

from pydantic_ai import Agent
from pydantic_ai.exceptions import UnexpectedModelBehavior
import logfire
import yaml
from dataclasses import dataclass
from typing import Optional, Any
from pathlib import Path

from code2verus.config import (
    get_error_template,
    load_translation_config,
    load_config,
)
from code2verus.tools import verus_tool, dafny_tool, lean_tool
from code2verus.utils import extract_rust_code, concatenate_yaml_fields
from code2verus.verification import verify_code
from code2verus.models import (
    TranslationDebugContext,
    ConversationExchange,
    VerificationError,
    AttemptResult,
    IterationStatus,
    TokenUsage,
    PromptConfiguration,
)


@dataclass
class TranslationResult:
    """Result of a code translation operation

    Attributes:
        output_content: The main translated content (YAML or target language code)
        num_iterations: Number of iterations taken during translation
        code_for_verification: Code used for verification (may differ from output_content for YAML)
        token_usage: Token usage statistics for the translation
        debug_context: Optional debug context containing detailed information about the translation process
    """

    output_content: str  # The main translated content (YAML or target language code)
    num_iterations: int  # Number of iterations taken
    code_for_verification: str  # Code used for verification
    token_usage: TokenUsage  # Token usage statistics
    debug_context: Optional[TranslationDebugContext] = (
        None  # Optional debug information
    )


def _update_conversation_history(result, current_history: list) -> list:
    """Update conversation history with new messages from agent result

    Args:
        result: Agent result containing new messages
        current_history: Current conversation history list

    Returns:
        Updated conversation history list
    """
    try:
        new_history = result.all_messages()
        if new_history and isinstance(new_history, list):
            logfire.info(f"Updated conversation history: {len(new_history)} messages")
            return new_history
        else:
            logfire.warning(f"Invalid conversation history format: {type(new_history)}")
            return current_history
    except (AttributeError, TypeError) as e:
        logfire.warning(f"Could not update conversation history: {e}")
        return current_history


def create_agent(source_language: str = "dafny", target_language: str = "verus"):
    """Create and return a configured PydanticAI agent with tools"""
    # Load translation-specific configuration
    translation_cfg = load_translation_config(
        source_language.lower(), target_language.lower()
    )

    # Extract configuration values from translation-specific config
    cfg_section = translation_cfg.get("config", {})
    system_prompts = translation_cfg.get("system_prompts", {})
    default_system = translation_cfg.get("system", "")

    # Load language-specific system prompt based on source language
    # The source language determines which translation rules to use
    language_prompt = system_prompts.get(source_language.lower(), default_system)

    # Select appropriate verification tools based on target language
    tools = []
    if target_language.lower() == "verus":
        tools.append(verus_tool)
    if target_language.lower() == "dafny" or source_language.lower() == "dafny":
        tools.append(dafny_tool)
    if target_language.lower() == "lean" or source_language.lower() == "lean":
        tools.append(lean_tool)

    # If no specific tools, include all for backward compatibility
    if not tools:
        tools = [verus_tool, dafny_tool, lean_tool]

    # Handle different model formats
    model_config = cfg_section["model"]
    final_model_config: Any  # Union of str or tuple for different model types

    # Check if this is an OpenRouter model configuration
    if model_config.startswith("openrouter:"):
        import os
        import importlib.util

        if importlib.util.find_spec("openai") is None:
            raise ImportError(
                "OpenAI package is required for OpenRouter models. "
                "Install it with: pip install openai"
            )

        # Extract the actual model name (e.g., "anthropic/claude-sonnet-4" from "openrouter:anthropic/claude-sonnet-4")
        openrouter_model = model_config[len("openrouter:") :]

        # Get OpenRouter API key
        api_key = os.getenv("OPENROUTER_API_KEY")
        if not api_key:
            raise ValueError(
                "OPENROUTER_API_KEY environment variable is required for OpenRouter models.\n"
                "You can set it by:\n"
                "1. Creating a .env file with: OPENROUTER_API_KEY=your-api-key\n"
                "2. Setting environment variable: export OPENROUTER_API_KEY=your-api-key\n"
                "\nGet your API key from: https://openrouter.ai/keys"
            )

        # Set OpenAI environment variables to configure PydanticAI for OpenRouter
        os.environ["OPENAI_API_KEY"] = api_key
        os.environ["OPENAI_BASE_URL"] = "https://openrouter.ai/api/v1"

        # Use PydanticAI's standard OpenAI model configuration
        # PydanticAI will use the environment variables to configure the client
        final_model_config = f"openai:{openrouter_model}"

        print(f"✓ Using OpenRouter model: {openrouter_model}")
        print("   Base URL: https://openrouter.ai/api/v1")
    else:
        final_model_config = model_config
        print(f"✓ Using model: {model_config}")

    return Agent(
        final_model_config,
        name=f"code_{source_language}2{target_language}",
        deps_type=str,  # Currently using str, could be enhanced to dict for richer context
        output_type=str,
        tools=tools,
        system_prompt=language_prompt,
        retries=10,
    )


async def translate_code_to_verus(
    source_code: str,
    source_language: str = "dafny",
    target_language: str = "verus",
    is_yaml: bool = False,
    max_iterations: int | None = None,
    fix_types: bool = False,
) -> TranslationResult:
    """Translate source code to target language using the agent with verification feedback

    Returns:
        TranslationResult: Contains output_content, num_iterations, and code_for_verification.
    """
    # Use config value if max_iterations not provided
    if max_iterations is None:
        # Load translation-specific config to get the correct max_iterations
        if fix_types:
            # Use the type fix configuration instead
            translation_cfg = load_config(
                Path(__file__).parent.parent.parent / "config" / "verus-type-fix.yml"
            )
        else:
            translation_cfg = load_translation_config(
                source_language.lower(), target_language.lower()
            )
        cfg_section = translation_cfg.get("config", {})
        max_iterations = cfg_section.get(
            "max_translation_iterations", 3
        )  # Default to 3 if not found

    # Type assertion to help type checker
    assert isinstance(max_iterations, int)

    # Create the agent once and reuse it throughout iterations
    # We maintain true conversational context using PydanticAI's message_history parameter
    # This ensures the agent remembers previous exchanges and can build upon them
    agent = create_agent(source_language, target_language)

    # Initialize variables with default values to ensure they're always defined
    result = None
    output_content = ""  # Will contain the final translated content
    code_for_verification = ""  # Will contain code for verification
    iteration = 0

    # Track conversation using proper message history for PydanticAI
    # This will be passed to agent.run() to maintain context across iterations
    conversation_history = []

    # Initialize structured debug context with type safety and validation
    debug_context = TranslationDebugContext(
        original_source=source_code,
        source_language=source_language,
        target_language=target_language,
        is_yaml=is_yaml,
        max_iterations=max_iterations,
    )

    # Log initial session information
    logfire.info(
        "Starting new translation session", extra=debug_context.to_summary_dict()
    )

    # Load translation-specific configuration for this context
    if fix_types:
        # Use the type fix configuration instead
        translation_cfg = load_config(
            Path(__file__).parent.parent.parent / "config" / "verus-type-fix.yml"
        )
    else:
        translation_cfg = load_translation_config(
            source_language.lower(), target_language.lower()
        )

    # Get language-specific prompts from translation config
    system_prompts = translation_cfg.get("system_prompts", {})
    yaml_instructions = translation_cfg.get("yaml_instructions", {})
    default_prompts = translation_cfg.get("default_prompts", {})

    if fix_types:
        # Use the specialized type fix prompts
        system_prompt = system_prompts.get("verus_type_fix", "")
        yaml_instruction = yaml_instructions.get("verus_type_fix", "")
        # Use a default prompt that's more generic for type fixing
        default_prompt = default_prompts.get("verus_type_fix", "")
    else:
        system_prompt = system_prompts.get(source_language.lower(), "")
        yaml_instruction = yaml_instructions.get(source_language.lower(), "")
        default_prompt = default_prompts.get(source_language.lower(), "")

    if is_yaml:
        logfire.info(
            f"Available yaml_instructions keys: {list(yaml_instructions.keys())}"
        )

        additional_prompt = yaml_instruction
        logfire.info(
            f"YAML mode for {source_language}, additional_prompt length: {len(additional_prompt)}"
        )
        logfire.debug(
            f"First 200 chars of additional_prompt: {additional_prompt[:200]}..."
        )
    else:
        additional_prompt = default_prompt
        logfire.info(
            f"Non-YAML mode for {source_language}, additional_prompt length: {len(additional_prompt)}"
        )

    # Capture prompt configuration for debugging
    validation_rules = translation_cfg.get("config", {}).get(
        "code_validation_rules", {}
    )
    lean_rules = (
        validation_rules.get("lean", []) if target_language.lower() == "lean" else []
    )

    prompt_config = PromptConfiguration(
        system_prompt=system_prompt,
        yaml_instructions=yaml_instruction,
        default_prompt=default_prompt,
        additional_prompt=additional_prompt,
        postcondition_mode=False,  # Always False since postcondition mode CLI was removed
        validation_rules_count=len(lean_rules),
    )

    # Store prompt configuration in debug context
    debug_context.set_prompt_configuration(prompt_config)

    logfire.info(
        f"Captured prompt configuration: system_prompt={len(system_prompt)} chars, "
        f"yaml_instructions={len(yaml_instruction)} chars, "
        f"default_prompt={len(default_prompt)} chars, "
        f"validation_rules={len(lean_rules)}"
    )

    # Log enforcement checks for Dafny-to-Lean
    if source_language.lower() == "dafny" and target_language.lower() == "lean":
        has_enforcement = all(
            [
                "CRITICAL ENFORCEMENT" in system_prompt,
                "CRITICAL YAML ENFORCEMENT" in yaml_instruction
                if is_yaml
                else "MANDATORY ENSURES MAPPING" in default_prompt,
                len(lean_rules) > 0,
            ]
        )
        logfire.info(f"Dafny-to-Lean enforcement active: {has_enforcement}")
        if not has_enforcement:
            logfire.warning("Missing enforcement rules in prompt configuration!")
            if "CRITICAL ENFORCEMENT" not in system_prompt:
                logfire.warning("System prompt missing CRITICAL ENFORCEMENT")
            if is_yaml and "CRITICAL YAML ENFORCEMENT" not in yaml_instruction:
                logfire.warning("YAML instructions missing CRITICAL YAML ENFORCEMENT")
            if not is_yaml and "MANDATORY ENSURES MAPPING" not in default_prompt:
                logfire.warning("Default prompt missing MANDATORY ENSURES MAPPING")
            if len(lean_rules) == 0:
                logfire.warning("No Lean validation rules configured")

    user_prompt = f"""
Please translate the following {source_language} code to {target_language}:

```{source_language.lower()}
{source_code}
```

{additional_prompt}
"""

    # Log initial translation setup
    logfire.info("Starting translation process:")
    logfire.info(f"Source language: {source_language}")
    logfire.info(f"Is YAML mode: {is_yaml}")
    logfire.info(f"Max iterations: {max_iterations}")
    logfire.info(f"Source code length: {len(source_code)} characters")
    logfire.info(f"Additional prompt length: {len(additional_prompt)} characters")
    logfire.debug(f"Initial user prompt:\n{user_prompt}")

    # Iterative improvement with verification feedback
    for iteration in range(max_iterations):
        logfire.info(f"Translation iteration {iteration + 1}/{max_iterations}")

        # Update debug context for current iteration
        debug_context.increment_iteration()

        # For the first iteration, use the original prompt
        if iteration == 0:
            current_prompt = user_prompt
        else:
            # For subsequent iterations, provide feedback based on previous errors
            # The conversation context will be maintained via message_history
            latest_error = debug_context.get_latest_error()
            if latest_error:
                current_prompt = get_error_template(
                    "verification_error",
                    source_lang=source_language,
                    target_lang=target_language,
                    verification_error=latest_error.error,
                    verification_output=latest_error.output or "",
                    source_language=source_language,
                    source_language_lower=source_language.lower(),
                    source_code=source_code,
                    additional_prompt=additional_prompt,
                )
            else:
                # Fallback to a generic improvement request
                current_prompt = "Please improve the previous translation to fix any issues and ensure it compiles with Verus."

        # Use deps to pass iteration context (for potential future tool enhancements)
        deps_context = f"iteration_{iteration + 1}_of_{max_iterations}"
        if debug_context.previous_attempts:
            deps_context += (
                f"_with_{len(debug_context.previous_attempts)}_previous_attempts"
            )

        # Log the prompt being sent to the agent
        logfire.info(f"Sending prompt to agent (iteration {iteration + 1}):")
        logfire.info(f"Prompt length: {len(current_prompt)} characters")
        logfire.debug(f"Full prompt:\n{current_prompt}")

        # Run the agent with proper message history to maintain conversation context
        # This is the key improvement: message_history maintains true conversational context
        try:
            result = await agent.run(
                current_prompt, message_history=conversation_history, deps=deps_context
            )
        except UnexpectedModelBehavior as e:
            logfire.error(
                f"OpenAI API returned unexpected response on iteration {iteration + 1}: {e}"
            )

            # If we have more iterations, try again with the next iteration
            if iteration < max_iterations - 1:
                logfire.info(
                    f"Retrying with next iteration ({iteration + 2}/{max_iterations})"
                )
                iteration += 1
                continue
            else:
                # If this was the last iteration, return a failed result
                logfire.error("All iterations exhausted due to API errors")
                debug_context.add_verification_error(
                    VerificationError(
                        iteration=iteration + 1,
                        error=f"OpenAI API error: {str(e)}",
                        error_type="api_error",
                    )
                )
                return TranslationResult(
                    output_content="",
                    num_iterations=iteration + 1,
                    code_for_verification="",
                    debug_context=debug_context,
                )

        # Capture token usage from the result
        iteration_token_usage = TokenUsage.from_run_usage(result.usage())
        debug_context.add_token_usage(iteration_token_usage)

        # Log the agent's response
        logfire.info(f"Received response from agent (iteration {iteration + 1}):")
        logfire.info(f"Response length: {len(result.output)} characters")
        logfire.info(
            f"Token usage - Input: {iteration_token_usage.input_tokens}, Output: {iteration_token_usage.output_tokens}, Total: {iteration_token_usage.total_tokens}"
        )
        logfire.debug(f"Full response:\n{result.output}")

        # Update conversation history with this exchange
        # Use the extracted method for better testability and error handling
        conversation_history = _update_conversation_history(
            result, conversation_history
        )

        # Store the conversation exchange for debugging using structured data
        exchange = ConversationExchange(
            iteration=iteration + 1,
            prompt=current_prompt,
            response=result.output,
            prompt_length=len(current_prompt),
            response_length=len(result.output),
            message_history_length=len(conversation_history)
            if isinstance(conversation_history, list)
            else 0,
            token_usage=iteration_token_usage,
        )
        debug_context.add_conversation_exchange(exchange)

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
                    # Track YAML error using structured data
                    yaml_error = VerificationError(
                        iteration=iteration + 1,
                        error=f"YAML syntax error: {str(e)}",
                        error_type="yaml_syntax",
                    )
                    debug_context.add_verification_error(yaml_error)

                    # If we have more iterations, prepare feedback to fix the YAML
                    yaml_error_feedback = get_error_template(
                        "yaml_syntax_error",
                        source_lang=source_language,
                        target_lang=target_language,
                        error=str(e),
                        source_language=source_language,
                        source_language_lower=source_language.lower(),
                        source_code=source_code,
                        additional_prompt=additional_prompt,
                    )
                    # Store this error feedback for next iteration
                    current_prompt = yaml_error_feedback

                    # Log the YAML error feedback that will be used in next iteration
                    logfire.warning(
                        "YAML syntax error occurred, preparing feedback for next iteration:"
                    )
                    logfire.debug(f"YAML error feedback prompt:\n{yaml_error_feedback}")

                    continue  # Skip verification and go to next iteration to fix YAML

            # Generate concatenated code from YAML for verification based on target language
            if target_language.lower() == "lean":
                from code2verus.utils import yaml_to_lean

                # CRITICAL ENFORCEMENT: Validate ensures -> solve_postcond mapping for Dafny-to-Lean
                if source_language.lower() == "dafny" and "ensures" in source_code:
                    # Check for postcondition definition
                    has_solve_postcond = "solve_postcond" in yaml_content
                    has_theorem = "theorem" in yaml_content

                    # Check that vc-theorems section is not empty
                    has_non_empty_theorems = False
                    # Look for vc-theorems section (either in vc-spec or as separate vc-theorems field)
                    theorems_section = ""
                    if "vc-theorems:" in yaml_content:
                        # New format: separate vc-theorems field
                        theorems_section = (
                            yaml_content.split("vc-theorems:")[1].split("\nvc-")[0]
                            if "vc-theorems:" in yaml_content
                            else ""
                        )
                    elif "vc-spec:" in yaml_content:
                        # Old format: vc-theorems inside vc-spec
                        spec_section = (
                            yaml_content.split("vc-spec:")[1]
                            if "vc-spec:" in yaml_content
                            else ""
                        )
                        if (
                            "-- <vc-theorems>" in spec_section
                            and "-- </vc-theorems>" in spec_section
                        ):
                            theorems_section = spec_section.split("-- <vc-theorems>")[
                                1
                            ].split("-- </vc-theorems>")[0]

                    # Check for actual theorem content in the theorems section
                    if theorems_section and (
                        "-- <vc-theorems>" in theorems_section
                        and "-- </vc-theorems>" in theorems_section
                    ):
                        theorems_content = (
                            theorems_section.split("-- <vc-theorems>")[1]
                            .split("-- </vc-theorems>")[0]
                            .strip()
                        )
                        has_non_empty_theorems = bool(
                            theorems_content and theorems_content != ""
                        )
                    elif theorems_section:
                        # Fallback: check if section has any meaningful content
                        clean_content = (
                            theorems_section.replace("|-", "")
                            .replace("-- <vc-theorems>", "")
                            .replace("-- </vc-theorems>", "")
                            .strip()
                        )
                        has_non_empty_theorems = bool(
                            clean_content and len(clean_content) > 0
                        )

                    if (
                        not has_solve_postcond
                        or not has_theorem
                        or not has_non_empty_theorems
                    ):
                        error_msg = "CRITICAL ENFORCEMENT VIOLATION: Dafny 'ensures' clause detected but Lean output incomplete:\n"
                        error_msg += f"- solve_postcond definition: {'✓' if has_solve_postcond else '✗'}\n"
                        error_msg += (
                            f"- theorem definition: {'✓' if has_theorem else '✗'}\n"
                        )
                        error_msg += f"- non-empty vc-theorems: {'✓' if has_non_empty_theorems else '✗'}\n"
                        error_msg += "This violates the mandatory ensures-to-postcondition mapping requirement."

                        logfire.error(error_msg)
                        logfire.error(
                            f"Source contains ensures: {'ensures' in source_code}"
                        )
                        logfire.error(f"YAML content preview:\n{yaml_content[:500]}...")

                        # Provide specific feedback to the AI about what's missing
                        feedback_parts = []
                        if not has_solve_postcond:
                            feedback_parts.append("missing 'solve_postcond' definition")
                        if not has_theorem:
                            feedback_parts.append(
                                "missing 'theorem solve_spec_satisfied'"
                            )
                        if not has_non_empty_theorems:
                            feedback_parts.append("empty '-- <vc-theorems>' section")

                        ai_feedback = f"ENFORCEMENT ERROR: The Dafny method has 'ensures' clauses but your output is {', '.join(feedback_parts)}. You MUST include both a 'solve_postcond' definition and a 'theorem solve_spec_satisfied' in the '-- <vc-theorems>' section."

                        # Create a verification error to force retry with specific feedback
                        debug_context.add_verification_error(
                            VerificationError(
                                iteration=iteration,
                                error=ai_feedback,
                                output="",
                                error_type="enforcement_violation",
                            )
                        )

                        logfire.warning(
                            f"Forcing retry due to enforcement violation: {ai_feedback}"
                        )
                        continue  # Skip verification and go to next iteration with enforcement feedback

                target_content = yaml_to_lean(yaml_content)
                logfire.info(
                    f"Converted YAML to Lean code ({len(target_content)} characters)"
                )
            elif target_language.lower() == "dafny":
                from code2verus.utils import yaml_to_dafny

                target_content = yaml_to_dafny(yaml_content)
                logfire.info(
                    f"Converted YAML to Dafny code ({len(target_content)} characters)"
                )
            else:
                # Default to Verus for backwards compatibility
                target_content = concatenate_yaml_fields(yaml_content)
                logfire.info(
                    f"Converted YAML to Verus code ({len(target_content)} characters)"
                )

            # For YAML mode, preserve the original YAML as main output
            # but use the converted target language code for verification
            output_content = yaml_content  # Keep original YAML for .yaml files
            code_for_verification = target_content  # Use converted code for .lean files
        else:
            # For regular files, extract code from markdown blocks
            output_content = extract_rust_code(result.output)
            code_for_verification = output_content  # Same content for both

        # Verify the generated code (except on the last iteration if we want to return regardless)
        if iteration < max_iterations - 1:
            (
                verification_success,
                verification_output,
                verification_error,
            ) = await verify_code(code_for_verification, target_language, is_yaml)

            # Track attempt results using structured data
            attempt_result = AttemptResult(
                iteration=iteration + 1,
                output_content=output_content,
                verification_success=verification_success,
                verification_error=verification_error
                if not verification_success
                else None,
                status=IterationStatus.SUCCESS
                if verification_success
                else IterationStatus.VERIFICATION_ERROR,
            )
            debug_context.add_attempt(attempt_result)

            if verification_success:
                logfire.info(f"Verification successful on iteration {iteration + 1}")
                logfire.info(
                    f"Successfully translated after {iteration + 1} iterations"
                )
                logfire.debug(f"Final successful output:\n{output_content}")
                break
            else:
                logfire.info(
                    f"Verification failed on iteration {iteration + 1}, trying to improve..."
                )
                # Track verification errors using structured data
                verification_error_obj = VerificationError(
                    iteration=iteration + 1,
                    error=verification_error,
                    output=verification_output,
                    error_type="verification",
                )
                debug_context.add_verification_error(verification_error_obj)

                # Prepare feedback for next iteration with specific error details
                feedback_prompt = get_error_template(
                    "verification_error",
                    source_lang=source_language,
                    target_lang=target_language,
                    verification_error=verification_error,
                    verification_output=verification_output,
                    source_language=source_language,
                    source_language_lower=source_language.lower(),
                    source_code=source_code,
                    additional_prompt=additional_prompt,
                )
                # Store this feedback for next iteration (will be enhanced with context)
                # The context building logic above will incorporate this feedback
                user_prompt = feedback_prompt

                # Log the verification error feedback
                logfire.warning(
                    "Verification failed, preparing feedback for next iteration:"
                )
                logfire.info(f"Verification error: {verification_error}")
                logfire.debug(f"Verification output: {verification_output}")
                logfire.debug(f"Error feedback prompt:\n{feedback_prompt}")

    # Return the actual number of iterations performed
    num_iterations = iteration + 1

    # Handle edge case where no iterations were performed
    if max_iterations == 0:
        logfire.warning("No iterations performed due to max_iterations=0")
        # Provide minimal fallback content
        output_content = f"# No translation performed (max_iterations=0)\n# Original {source_language} code:\n{source_code}"
        code_for_verification = "// No verification possible - no iterations performed"
        num_iterations = 0

    # Mark debug session as completed
    debug_context.mark_completed()

    # Log final summary of the translation process using structured debug context
    summary = debug_context.to_summary_dict()
    logfire.info("Translation process completed", extra=summary)

    logfire.info(f"Translation completed after {num_iterations} iterations")
    logfire.info(f"Final output length: {len(output_content)} characters")
    logfire.info(
        f"Total conversation exchanges: {len(debug_context.conversation_exchanges)}"
    )
    logfire.info(
        f"Final conversation history length: {len(conversation_history) if isinstance(conversation_history, list) else 0} messages"
    )

    # Log conversation summary using structured data
    conversation_summary = "Conversation Summary:\n"
    for i, exchange in enumerate(debug_context.conversation_exchanges):
        conversation_summary += f"Exchange {i + 1} (Iteration {exchange.iteration}):\n"
        conversation_summary += f"  - Prompt: {exchange.prompt_length} chars\n"
        conversation_summary += f"  - Response: {exchange.response_length} chars\n"
        conversation_summary += (
            f"  - Message history: {exchange.message_history_length} messages\n"
        )

    logfire.info(conversation_summary)

    # Log verification attempts summary using structured data
    if debug_context.verification_errors:
        logfire.info(
            f"Verification errors encountered: {len(debug_context.verification_errors)}"
        )
        for i, error in enumerate(debug_context.verification_errors):
            logfire.debug(
                f"Error {i + 1} (Iteration {error.iteration}): {error.error[:100]}..."
            )

    logfire.debug(f"Final translated output:\n{output_content}")

    return TranslationResult(
        output_content=output_content,
        num_iterations=num_iterations,
        code_for_verification=code_for_verification,
        token_usage=debug_context.total_token_usage,
        debug_context=debug_context,
    )
