"""Code extraction and fixing utilities."""

import logging
import re

from ..core.config import ProcessingConfig

logger = logging.getLogger(__name__)


def extract_code(config: ProcessingConfig, output: str) -> str:
    """Extract code from LLM response based on current language.

    This function intentionally avoids any language-specific post-processing
    of incomplete code. It returns the extracted code verbatim.
    """
    # First try to extract from code blocks
    for pattern in config.language_config.code_block_patterns:
        code_block_match = re.search(
            rf"```{pattern}\n(.*?)```", output, re.DOTALL | re.IGNORECASE
        )
        if code_block_match:
            code = code_block_match.group(1).strip()
            return code

    # Generic code block
    code_block_match = re.search(r"```\n(.*?)```", output, re.DOTALL)
    if code_block_match:
        code = code_block_match.group(1).strip()
        return code

    # If no code block, try to find language-specific code patterns
    lines = output.split("\n")
    code_lines = []
    in_code = False

    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (
            line.strip().startswith("Looking at")
            or line.strip().startswith("The errors show that:")
            or line.strip().startswith("The issue is in")
            or line.strip().startswith("This function will be")
            or line.strip().startswith("Below is a")
            or line.strip().startswith("Theo note:")
            or line.strip().startswith("// This function will be")
            or line.strip().startswith("// Below is a")
            or line.strip().startswith("// Theo note:")
            or line.strip().startswith("```")
            or re.match(r"^\d+\.", line.strip())
        ):
            continue

        # Start collecting when we see language keywords
        for keyword in config.language_config.keywords:
            if keyword in line:
                in_code = True
                break

        if in_code:
            code_lines.append(line)

    if code_lines:
        code = "\n".join(code_lines).strip()
        return code

    # Fallback: return the original output but cleaned
    code = output.strip()
    return code




def verify_spec_preservation(
    config: ProcessingConfig, original_code: str, generated_code: str
) -> bool:
    """Verify that all specifications from the original code are preserved in the generated code."""
    if not config.strict_spec_verification:
        return True

    for pattern in config.language_config.spec_patterns:
        original_specs = re.findall(pattern, original_code, re.DOTALL)

        for spec in original_specs:
            spec_content = spec.strip()

            # Normalize whitespace for comparison
            normalized_spec = re.sub(r"\s+", " ", spec_content)
            normalized_generated = re.sub(r"\s+", " ", generated_code)

            # Check if the normalized content is present
            if normalized_spec not in normalized_generated:
                logger.warning(
                    "Specification missing or modified: %s...", spec_content[:100]
                )
                return False

    return True


def restore_specs(
    config: ProcessingConfig, original_code: str, generated_code: str
) -> str:
    """Restore original specifications in the generated code."""
    # This is a simplified version - you may need to customize for each language
    # For now, we'll just prepend the original specs
    result = []

    # Extract all specs from original
    all_specs = []
    for pattern in config.language_config.spec_patterns:
        specs = re.findall(f"({pattern})", original_code, re.DOTALL)
        all_specs.extend(specs)

    if all_specs:
        # Add original specs at the beginning
        for spec in all_specs:
            result.append(spec[0].strip())
            result.append("")

        # Add generated code
        result.append(generated_code)
        return "\n".join(result)

    return generated_code
