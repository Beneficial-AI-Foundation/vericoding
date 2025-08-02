"""Code extraction and fixing utilities."""

import re

from ..core.config import ProcessingConfig
from ..utils.io_utils import thread_safe_print


def extract_code(config: ProcessingConfig, output: str) -> str:
    """Extract code from LLM response based on current language."""
    # First try to extract from code blocks
    for pattern in config.language_config.code_block_patterns:
        code_block_match = re.search(
            rf"```{pattern}\n(.*?)```", output, re.DOTALL | re.IGNORECASE
        )
        if code_block_match:
            code = code_block_match.group(1).strip()
            code = fix_incomplete_code(config, code)
            return code

    # Generic code block
    code_block_match = re.search(r"```\n(.*?)```", output, re.DOTALL)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(config, code)
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
        code = fix_incomplete_code(config, code)
        return code

    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(config, code)
    return code


def fix_incomplete_code(config: ProcessingConfig, code: str) -> str:
    """Fix common incomplete code patterns based on language."""
    if config.language == "verus":
        return fix_incomplete_verus_code(code)
    elif config.language == "dafny":
        return fix_incomplete_dafny_code(code)
    elif config.language == "lean":
        return fix_incomplete_lean_code(code)
    return code


def fix_incomplete_verus_code(code: str) -> str:
    """Fix incomplete Verus code patterns."""
    lines = code.split("\n")
    fixed_lines = []
    in_verus_block = False

    for i, line in enumerate(lines):
        # Track verus! block
        if "verus!" in line:
            in_verus_block = True
        elif line.strip() == "} // verus!" or (line.strip() == "}" and in_verus_block):
            in_verus_block = False

        # Fix incomplete function bodies (non-spec functions)
        if (
            (line.strip().startswith("fn ") or line.strip().startswith("proof fn "))
            and "{" not in line
            and not line.strip().endswith(";")
        ):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if (
                    "{" in lines[j]
                    or lines[j].strip().startswith("unimplemented!")
                    or lines[j].strip().startswith("return")
                ):
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("fn ")
                    or lines[j].strip().startswith("spec fn")
                    or lines[j].strip().startswith("proof fn")
                ):
                    break
            if not has_body:
                # Add empty body with TODO comment
                fixed_lines.append(line)
                fixed_lines.append("{")
                fixed_lines.append(
                    "    return false;  // TODO: Remove this line and implement the function body"
                )
                fixed_lines.append("}")
                continue

        # Fix incomplete spec function bodies
        if (
            line.strip().startswith("spec fn ")
            and "{" not in line
            and not line.strip().endswith(";")
        ):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if "{" in lines[j] or lines[j].strip() == ";":
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("fn ")
                    or lines[j].strip().startswith("spec fn")
                    or lines[j].strip().startswith("proof fn")
                ):
                    break
            if not has_body:
                # Add semicolon for spec functions without body
                fixed_lines.append(line + ";")
                continue

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


def fix_incomplete_dafny_code(code: str) -> str:
    """Fix incomplete Dafny code patterns."""
    lines = code.split("\n")
    fixed_lines = []

    for _i, line in enumerate(lines):
        # Fix incomplete strings in Dafny
        if ':= "' in line and not line.strip().endswith('"'):
            line = (
                line.rstrip() + '""'
                if line.strip().endswith(':= "')
                else line.rstrip() + '"'
            )

        # Fix incomplete variable declarations
        if "var " in line and " := " in line and not line.endswith(";"):
            if not line.strip().endswith("}"):
                line = line.rstrip() + ";"

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


def fix_incomplete_lean_code(code: str) -> str:
    """Fix incomplete Lean code patterns."""
    lines = code.split("\n")
    fixed_lines = []

    for i, line in enumerate(lines):
        # Fix incomplete sorry statements
        if "sorry" not in line and (
            line.strip().startswith("theorem ")
            or line.strip().startswith("lemma ")
            or line.strip().startswith("def ")
        ):
            # Look ahead to see if there's a body
            has_body = False
            for j in range(i + 1, len(lines)):
                if ":=" in lines[j] or "sorry" in lines[j] or "where" in lines[j]:
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("theorem ")
                    or lines[j].strip().startswith("lemma ")
                    or lines[j].strip().startswith("def ")
                ):
                    break
            if not has_body and ":" in line:
                # Add sorry for incomplete theorems/lemmas
                fixed_lines.append(line)
                fixed_lines.append("  sorry")
                continue

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


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
                thread_safe_print(
                    f"    ⚠️  Specification missing or modified: {spec_content[:100]}..."
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
