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
import logfire
import yaml
from dataclasses import dataclass
from typing import Optional, Any

from code2verus.config import (
    system_prompt,
    cfg,
    full_cfg,
    get_config_value,
    get_error_template,
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
)


@dataclass
class TranslationResult:
    """Result of a code translation operation

    Attributes:
        output_content: The main translated content (YAML or target language code)
        num_iterations: Number of iterations taken during translation
        code_for_verification: Code used for verification (may differ from output_content for YAML)
        debug_context: Optional debug context containing detailed information about the translation process
    """

    output_content: str  # The main translated content (YAML or target language code)
    num_iterations: int  # Number of iterations taken
    code_for_verification: str  # Code used for verification
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
    # Load language-specific system prompt based on source language
    # The source language determines which translation rules to use
    language_prompt = full_cfg.get("system_prompts", {}).get(
        source_language.lower(), system_prompt
    )

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
    model_config = cfg["model"]
    final_model_config: Any  # Union of str or tuple for different model types

    # Check if this is an OpenRouter model configuration
    if model_config.startswith("openrouter:"):
        import os

        try:
            from openai import OpenAI
        except ImportError:
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

        # Create OpenAI client configured for OpenRouter
        client = OpenAI(
            api_key=api_key,
            base_url="https://openrouter.ai/api/v1",
        )

        # Use OpenAI format with custom client for PydanticAI
        final_model_config = ("openai", openrouter_model, client)

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
) -> TranslationResult:
    """Translate source code to target language using the agent with verification feedback

    Returns:
        TranslationResult: Contains output_content, num_iterations, and code_for_verification.
    """
    # Use config value if max_iterations not provided
    if max_iterations is None:
        max_iterations = get_config_value("max_translation_iterations")

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
        result = await agent.run(
            current_prompt, message_history=conversation_history, deps=deps_context
        )

        # Log the agent's response
        logfire.info(f"Received response from agent (iteration {iteration + 1}):")
        logfire.info(f"Response length: {len(result.output)} characters")
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

            # Also generate concatenated Rust code from YAML for verification
            rust_content = concatenate_yaml_fields(yaml_content)
            logfire.info(f"Concatenated Rust code length: {len(rust_content)}")

            # Return YAML content as main output, Rust content as secondary
            output_content = yaml_content
            code_for_verification = rust_content
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
        debug_context=debug_context,
    )
