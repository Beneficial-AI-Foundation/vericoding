"""Code extraction and fixing utilities."""

import json
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


def apply_json_replacements(config: ProcessingConfig, original_code: str, llm_response: str) -> tuple[str, str | None]:
    """Apply JSON array of replacements to original code.
    
    Securely replaces only 'sorry' (Lean) or content within <vc-code> tags (Dafny/Verus).
    LLM is untrusted - we validate everything and control where replacements go.
    
    Returns:
        tuple[str, str | None]: (modified_code, error_message)
        If error_message is not None, this should be treated as a verification failure.
    """
    try:
        # Extract JSON array from response
        json_match = re.search(r'```json\s*(.*?)\s*```', llm_response, re.DOTALL | re.IGNORECASE)
        if not json_match:
            # Try to find JSON array without code block
            json_match = re.search(r'\[.*?\]', llm_response, re.DOTALL)
        
        if not json_match:
            error = "JSON parsing failed: No JSON array found in LLM response"
            logger.error(error)
            return original_code, error
            
        json_str = json_match.group(1) if json_match.group(1) else json_match.group(0)
        replacements = json.loads(json_str)
        
        if not isinstance(replacements, list):
            error = "JSON parsing failed: Expected JSON array, got something else"
            logger.error(error)
            return original_code, error
        
        # Find all placeholders in the original code that we're allowed to replace
        if config.language == "lean":
            # For Lean: find all 'sorry' occurrences
            placeholder_positions = []
            code_copy = original_code
            search_start = 0
            while True:
                pos = code_copy.find("sorry", search_start)
                if pos == -1:
                    break
                placeholder_positions.append(pos)
                search_start = pos + 1
                
            expected_count = len(placeholder_positions)
            
        else:
            # For Dafny/Verus: find all <vc-code> sections
            vc_code_pattern = r'<vc-code>(.*?)</vc-code>'
            vc_code_matches = list(re.finditer(vc_code_pattern, original_code, re.DOTALL))
            expected_count = len(vc_code_matches)
        
        # Validate replacement count
        if len(replacements) != expected_count:
            error = f"JSON replacement count mismatch: Expected {expected_count} replacements for {expected_count} placeholders, got {len(replacements)}"
            logger.error(error)
            return original_code, error
        
        if expected_count == 0:
            logger.info("  ✓ No placeholders found to replace")
            return original_code, None
            
        # Apply replacements securely in reverse order to preserve positions
        modified_code = original_code
        
        if config.language == "lean":
            # Replace 'sorry' in reverse order (last first) to preserve positions
            for i in range(len(replacements) - 1, -1, -1):
                replacement = replacements[i]
                if not isinstance(replacement, str):
                    error = f"JSON parsing failed: Replacement {i} must be a string, got {type(replacement)}"
                    logger.error(error)
                    return original_code, error
                    
                # Find the i-th sorry (0-indexed)
                sorry_count = 0
                pos = 0
                target_pos = -1
                while pos < len(modified_code):
                    next_pos = modified_code.find("sorry", pos)
                    if next_pos == -1:
                        break
                    if sorry_count == i:
                        target_pos = next_pos
                        break
                    sorry_count += 1
                    pos = next_pos + 1
                
                if target_pos == -1:
                    error = f"JSON replacement failed: Could not find sorry #{i} for replacement"
                    logger.error(error)
                    return original_code, error
                
                # Replace this specific 'sorry'
                modified_code = modified_code[:target_pos] + replacement + modified_code[target_pos + 5:]
                
        else:
            # Replace <vc-code> sections in reverse order to preserve positions
            for i in range(len(vc_code_matches) - 1, -1, -1):
                replacement = replacements[i]
                if not isinstance(replacement, str):
                    error = f"JSON parsing failed: Replacement {i} must be a string, got {type(replacement)}"
                    logger.error(error)
                    return original_code, error
                
                match = vc_code_matches[i]
                start_tag_end = match.start() + 9  # length of "<vc-code>"
                end_tag_start = match.end() - 10   # length of "</vc-code>"
                
                # Replace only the content between tags, not the tags themselves
                modified_code = modified_code[:start_tag_end] + replacement + modified_code[end_tag_start:]
        
        # Final verification - ensure no placeholders remain
        if config.language == "lean":
            remaining_sorries = modified_code.count("sorry")
            if remaining_sorries > 0:
                error = f"JSON replacement failed: {remaining_sorries} 'sorry' placeholders still remain after replacement"
                logger.error(error)
                return original_code, error
        else:
            remaining_sections = len(re.findall(r'<vc-code>.*?</vc-code>', modified_code, re.DOTALL))
            if remaining_sections > 0:
                error = f"JSON replacement failed: {remaining_sections} <vc-code> sections still contain placeholder content"
                logger.error(error)
                return original_code, error
                    
        logger.info(f"  ✓ Successfully applied {len(replacements)} JSON replacements")
        return modified_code, None
        
    except json.JSONDecodeError as e:
        error = f"JSON parsing failed: Invalid JSON syntax - {str(e)}"
        logger.error(error)
        return original_code, error
    except Exception as e:
        error = f"JSON replacement failed: Unexpected error - {str(e)}"
        logger.error(error)
        return original_code, error
