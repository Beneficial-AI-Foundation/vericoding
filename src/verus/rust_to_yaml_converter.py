#!/usr/bin/env python3
"""
Convert Rust Verus files to YAML format following the vericoding template.
"""

import re
from pathlib import Path
from typing import Dict
import argparse


def parse_return_type(signature: str) -> str:
    """Parse the return type from a function signature."""
    # Look for -> (return_type) pattern, handling nested parentheses properly
    arrow_pos = signature.find("->")
    if arrow_pos == -1:
        return "()"

    # Start from after the arrow
    search_start = arrow_pos + 2

    # Skip whitespace
    while search_start < len(signature) and signature[search_start].isspace():
        search_start += 1

    if search_start >= len(signature):
        return "()"

    # Check if we have parentheses around the return type
    if signature[search_start] == "(":
        # Find the matching closing parenthesis, handling nested parens
        paren_count = 1
        search_pos = search_start + 1

        while search_pos < len(signature) and paren_count > 0:
            char = signature[search_pos]
            if char == "(":
                paren_count += 1
            elif char == ")":
                paren_count -= 1
            search_pos += 1

        if paren_count == 0:
            # Extract the content inside the parentheses
            return_content = signature[search_start + 1 : search_pos - 1].strip()
        else:
            # Unmatched parentheses, fall back to simple parsing
            return "()"
    else:
        # No parentheses, find the end of the return type
        end_patterns = ["\n", "ensures", "requires", "where", "{"]
        end_pos = len(signature)

        for pattern in end_patterns:
            pos = signature.find(pattern, search_start)
            if pos != -1 and pos < end_pos:
                end_pos = pos

        return_content = signature[search_start:end_pos].strip()

    # Handle binding names and tuple field names
    if ":" in return_content:
        # Case 1: Simple binding like "result: Type" (no nested structure)
        colon_pos = return_content.find(":")
        before_colon = return_content[:colon_pos].strip()
        after_colon = return_content[colon_pos + 1 :].strip()

        # If what's before the colon is a simple identifier and what's after looks like a type
        if before_colon.isidentifier() and (
            after_colon.startswith("(")  # tuple type
            or after_colon
            in [
                "i8",
                "i16",
                "i32",
                "i64",
                "i128",
                "isize",
                "u8",
                "u16",
                "u32",
                "u64",
                "u128",
                "usize",
                "bool",
                "String",
                "f32",
                "f64",
                "char",
            ]  # simple types
            or after_colon.startswith("Vec<")  # Vec types
            or after_colon.startswith("Option<")  # Option types
            or after_colon.startswith("&")
        ):  # Reference types
            return_content = after_colon
        # Case 2: Tuple with named fields like "(a: i32, b: i32)"
        elif return_content.startswith("(") and return_content.endswith(")"):
            # This shouldn't happen since we extracted content from inside parens already
            pass
        # Case 3: We have content that WAS inside parens and may have named fields
        elif "," in return_content:
            # This looks like tuple fields, process each element
            elements = []
            current_element = ""
            paren_depth = 0

            for char in return_content + ",":  # Add comma to handle last element
                if char == "," and paren_depth == 0:
                    element = current_element.strip()
                    if element:
                        # Remove field name if present (e.g., "a: i32" -> "i32")
                        if ":" in element:
                            colon_idx = element.find(":")
                            field_name = element[:colon_idx].strip()
                            field_type = element[colon_idx + 1 :].strip()
                            if field_name.isidentifier():
                                element = field_type
                        elements.append(element)
                    current_element = ""
                else:
                    current_element += char
                    if char == "(":
                        paren_depth += 1
                    elif char == ")":
                        paren_depth -= 1

            if elements:
                return_content = f"({', '.join(elements)})"

    # Final check: if we have comma-separated content that doesn't have parens, add them
    if "," in return_content and not return_content.startswith("("):
        return_content = f"({return_content})"

    return return_content if return_content else "()"


def generate_default_value(return_type: str) -> str:
    """Generate a default value for a given return type."""
    # Normalize the return type
    return_type = return_type.strip()

    # Handle common types
    if return_type in ["()", "unit"]:
        return "()"
    elif return_type == "bool":
        return "false"
    elif return_type in [
        "u8",
        "u16",
        "u32",
        "u64",
        "u128",
        "usize",
        "i8",
        "i16",
        "i32",
        "i64",
        "i128",
        "isize",
    ]:
        return "0"
    elif return_type in ["f32", "f64"]:
        return "0.0"
    elif return_type == "char":
        return "'\\0'"
    elif return_type.startswith("Vec<"):
        return "vec![]"
    elif return_type.startswith("Option<"):
        return "None"
    elif return_type.startswith("Result<"):
        return "Err(())"
    elif return_type == "String":
        return "String::new()"
    elif return_type.startswith("&Vec<"):
        # For reference types in stubs, we can't return a reference to a temporary
        # Use assume(false) and a dummy reference (this is stub code)
        return "{ assume(false); &vec![] }"
    elif return_type == "&str":
        return '""'
    elif return_type.startswith("&"):
        # General reference types - use assume(false) and unsafe pointer cast
        return "{ assume(false); unsafe { &*(std::ptr::null() as *const _) } }"
    elif return_type.startswith("(") and return_type.endswith(")"):
        # Tuple type
        if return_type == "()":
            return "()"
        # Parse tuple elements and generate defaults for each
        inner = return_type[1:-1].strip()  # Remove outer parens
        if not inner:
            return "()"

        # Split by comma, being careful about nested types
        elements = []
        current_element = ""
        paren_depth = 0
        angle_depth = 0

        for char in inner + ",":  # Add comma to handle last element
            if char == "," and paren_depth == 0 and angle_depth == 0:
                if current_element.strip():
                    elements.append(current_element.strip())
                current_element = ""
            else:
                current_element += char
                if char == "(":
                    paren_depth += 1
                elif char == ")":
                    paren_depth -= 1
                elif char == "<":
                    angle_depth += 1
                elif char == ">":
                    angle_depth -= 1

        if not elements:
            return "()"

        # Generate default values for each tuple element
        default_elements = []
        for element in elements:
            try:
                default_elements.append(generate_default_value(element))
            except ValueError:
                # If we can't generate a default for any element, use a simple default
                if element.strip() in ["usize", "u32", "u64", "i32", "i64", "isize"]:
                    default_elements.append("0")
                elif element.strip() == "bool":
                    default_elements.append("false")
                else:
                    # For unknown types, use a simple default that might work
                    default_elements.append("Default::default()")

        return f"({', '.join(default_elements)})"
    else:
        # For unknown types, fail the conversion
        raise ValueError(
            f"Cannot generate default value for unknown return type: {return_type}"
        )


def extract_proof_and_spec_functions(content: str) -> tuple[str, list[str], list[str]]:
    """Extract proof functions and spec functions from content, leave proof blocks inside functions."""
    proof_functions = []
    spec_functions = []
    extracted_regions = []  # Track (start, end) of extracted regions

    # Find proof functions and spec functions (not proof blocks)
    pos = 0
    while pos < len(content):
        # Look for 'proof fn' or 'spec fn'
        proof_fn_match = re.search(r"proof\s+fn\s+", content[pos:])
        spec_fn_match = re.search(r"spec\s+fn\s+", content[pos:])

        # Find the earliest match
        earliest_match = None
        earliest_pos = float("inf")
        match_type = None

        if proof_fn_match and pos + proof_fn_match.start() < earliest_pos:
            earliest_pos = pos + proof_fn_match.start()
            earliest_match = proof_fn_match
            match_type = "proof"

        if spec_fn_match and pos + spec_fn_match.start() < earliest_pos:
            earliest_pos = pos + spec_fn_match.start()
            earliest_match = spec_fn_match
            match_type = "spec"

        if not earliest_match:
            break

        # Find the opening brace of the function body
        brace_search_start = pos + earliest_match.end()
        brace_match = re.search(r"\{", content[brace_search_start:])
        if not brace_match:
            pos = pos + earliest_match.end()
            continue

        brace_pos = brace_search_start + brace_match.start()

        # Look backwards to include attributes and comments that belong to this function
        construct_start = earliest_pos
        lines_before = content[:construct_start].split("\n")

        # Go backwards through lines to find where the function really starts
        function_start_line_idx = len(lines_before) - 1

        # Skip empty lines and find the last non-empty line before the function
        while (
            function_start_line_idx >= 0
            and not lines_before[function_start_line_idx].strip()
        ):
            function_start_line_idx -= 1

        # Check if there are attributes or comments that belong to this function
        while function_start_line_idx >= 0:
            line = lines_before[function_start_line_idx].strip()
            # If this line is an attribute, comment, or empty line that should be included
            if line.startswith("#[") or line.startswith("//") or not line:
                function_start_line_idx -= 1
            else:
                # This line doesn't belong to the function, stop here
                break

        # Calculate the actual start position
        if function_start_line_idx < 0:
            # All lines before belong to the function
            construct_start = 0
        else:
            # Start after the last line that doesn't belong to the function
            construct_start = len(
                "\n".join(lines_before[: function_start_line_idx + 1])
            )
            if construct_start > 0:
                construct_start += 1  # Account for the newline character

        # Find the matching closing brace
        brace_count = 1
        search_pos = brace_pos + 1

        while search_pos < len(content) and brace_count > 0:
            if content[search_pos] == "{":
                brace_count += 1
            elif content[search_pos] == "}":
                brace_count -= 1
            search_pos += 1

        if brace_count == 0:
            # Found complete function, now look for trailing comments that belong to it
            construct_end = search_pos

            # Look forward for trailing comments (like "// pure-end", "// impl-end")
            lines_after = content[search_pos:].split("\n")
            trailing_lines = []

            for line_idx, line in enumerate(lines_after):
                line_stripped = line.strip()
                # Check if this is a trailing comment that belongs to the function
                if line_stripped.startswith("//") and (
                    line_stripped.endswith("-end")
                    or line_stripped.endswith("pure-end")
                    or line_stripped.endswith("impl-end")
                    or line_stripped.endswith("spec-end")
                ):
                    trailing_lines.append(line)
                elif not line_stripped:  # Empty line
                    trailing_lines.append(line)
                else:
                    # Non-empty, non-trailing-comment line - stop here
                    break

            # Calculate new end position including trailing comments
            if trailing_lines:
                # Find the last non-empty trailing line
                last_content_idx = -1
                for i in range(len(trailing_lines) - 1, -1, -1):
                    if trailing_lines[i].strip():
                        last_content_idx = i
                        break

                if last_content_idx >= 0:
                    # Include up to and including the last meaningful trailing line
                    trailing_content = "\n".join(trailing_lines[: last_content_idx + 1])
                    construct_end = search_pos + len(trailing_content)

            # Extract the complete function including trailing comments
            construct = content[construct_start:construct_end]
            # Clean up indentation while preserving structure
            lines = construct.split("\n")
            if lines:
                # Find minimum indentation (excluding empty lines)
                min_indent = float("inf")
                for line in lines:
                    if line.strip():  # Skip empty lines
                        indent = len(line) - len(line.lstrip())
                        min_indent = min(min_indent, indent)

                # Remove common indentation from all lines
                if min_indent != float("inf"):
                    cleaned_lines = []
                    for line in lines:
                        if line.strip():  # Non-empty line
                            cleaned_lines.append(
                                line[min_indent:]
                                if len(line) >= min_indent
                                else line.lstrip()
                            )
                        else:  # Empty line
                            cleaned_lines.append("")
                    construct = "\n".join(cleaned_lines).strip()

            if match_type == "proof":
                proof_functions.append(construct)
            else:  # match_type == 'spec'
                spec_functions.append(construct)

            # Track the extracted region
            extracted_regions.append((construct_start, construct_end))
            pos = construct_end
        else:
            # Unmatched braces, skip this match
            pos = pos + earliest_match.end()

    # Build cleaned content by excluding extracted regions
    cleaned_content = ""
    last_end = 0

    # Sort regions by start position
    extracted_regions.sort(key=lambda x: x[0])

    for start, end in extracted_regions:
        # Add content between previous extraction and this one
        cleaned_content += content[last_end:start]
        last_end = end

    # Add any remaining content after the last extraction
    cleaned_content += content[last_end:]

    # Clean up extra whitespace
    cleaned_content = re.sub(r"\n\s*\n\s*\n", "\n\n", cleaned_content)

    return cleaned_content.strip(), proof_functions, spec_functions


def parse_rust_file(content: str) -> Dict[str, str]:
    """Parse a Rust file and extract the different sections for YAML conversion."""

    # Don't extract main function at the beginning - handle it later with postamble
    content = content.rstrip()

    # Extract imports and opening verus block (preamble)
    preamble_pattern = r"^(.*?verus!\s*\{)\s*"
    preamble_match = re.match(preamble_pattern, content, re.DOTALL)

    if not preamble_match:
        raise ValueError("Could not find verus! block opening")

    preamble_base = preamble_match.group(1)
    remaining_content = content[preamble_match.end() :]

    # Extract proof functions and spec functions (not proof blocks) from the remaining content
    remaining_content, proof_functions, spec_functions = (
        extract_proof_and_spec_functions(remaining_content)
    )

    # Build preamble: imports + verus opening + spec functions
    preamble_parts = [preamble_base]
    if spec_functions:
        preamble_parts.append("")  # Add empty line before spec functions
        for spec_fn in spec_functions:
            preamble_parts.append(spec_fn)
    preamble = "\n".join(preamble_parts) + "\n"

    # Find all normal function declarations (excluding main)
    fn_pattern = r"fn\s+(?!main\b)\w+"
    fn_matches = list(re.finditer(fn_pattern, remaining_content))

    if len(fn_matches) == 0:
        raise ValueError("Could not find any function declarations")

    # Find the last normal function for spec/code split
    last_fn_match = fn_matches[-1]

    # Extract all functions before the last one
    other_functions = []
    if len(fn_matches) > 1:
        # Find the start of the last function
        last_fn_start = last_fn_match.start()

        # Look backwards to include any comments/attributes
        # We need to find attributes like #[...] that should be part of the function
        lines_before = remaining_content[:last_fn_start].split("\n")

        # Go backwards through lines to find where the function really starts
        function_start_line_idx = len(lines_before) - 1

        # Skip empty lines and find the last non-empty line before the function
        while (
            function_start_line_idx >= 0
            and not lines_before[function_start_line_idx].strip()
        ):
            function_start_line_idx -= 1

        # Check if there are attributes or comments that belong to this function
        while function_start_line_idx >= 0:
            line = lines_before[function_start_line_idx].strip()
            # If this line is an attribute, comment, or empty line that should be included
            if line.startswith("#[") or line.startswith("//") or not line:
                function_start_line_idx -= 1
            else:
                # This line doesn't belong to the function, stop here
                break

        # Calculate the actual start position
        if function_start_line_idx < 0:
            # All lines before belong to the function
            last_fn_start = 0
        else:
            # Start after the last line that doesn't belong to the function
            last_fn_start = len("\n".join(lines_before[: function_start_line_idx + 1]))
            if last_fn_start > 0:
                last_fn_start += 1  # Account for the newline character

        # Extract all content before the last function (contains other functions)
        before_last_fn = remaining_content[:last_fn_start].strip()
        if before_last_fn:
            other_functions.append(before_last_fn)

        # Process only the last function
        last_fn_content = remaining_content[last_fn_start:]
    else:
        # Single function case
        last_fn_content = remaining_content

    # Improved parsing: find the complete function, then find its final closing brace
    # and count backwards to find the matching opening brace
    fn_start = re.search(r"fn\s+\w+", last_fn_content)
    if not fn_start:
        raise ValueError("Could not find function declaration")

    # We need to find the function body braces, not all braces
    # The function body is what comes AFTER the function signature and ensures/requires
    function_body_start = -1
    function_body_end = -1

    # Find all opening and closing braces, but only consider those that could be function body braces
    # Look for braces that come after the function signature
    brace_positions = []
    for i, char in enumerate(last_fn_content):
        if char == "{":
            brace_positions.append((i, "open"))
        elif char == "}":
            brace_positions.append((i, "close"))

    if not brace_positions:
        raise ValueError("Could not find any braces in function")

    # Strategy: find the last balanced brace pair in the function content
    # This should be the function body braces
    # We work backwards through closing braces to find one that matches properly

    # But we need to exclude braces that belong to the larger structure (like verus! block)
    # We'll look for the first brace that appears after the function signature

    # Find where the function signature likely ends (after ensures/requires clauses)
    signature_end = fn_start.end()

    # Look for the first opening brace that comes after the function signature
    # But be careful not to pick braces inside ensures/requires clauses
    first_open_after_signature = -1

    # Strategy: Look for a brace that appears at the start of a line (with only whitespace before it)
    # This is more likely to be the function body opening brace
    for i, (pos, brace_type) in enumerate(brace_positions):
        if brace_type == "open" and pos > signature_end:
            # Check if this brace starts a line (or has only whitespace before it)
            line_start = last_fn_content.rfind("\n", 0, pos)
            if line_start == -1:
                line_start = 0
            else:
                line_start += 1  # Move past the newline

            before_brace = last_fn_content[line_start:pos]
            if before_brace.strip() == "":
                # This brace starts a line (only whitespace before it)
                first_open_after_signature = i
                break

    # Fallback: if no line-starting brace found, use the first brace after signature
    if first_open_after_signature == -1:
        for i, (pos, brace_type) in enumerate(brace_positions):
            if brace_type == "open" and pos > signature_end:
                first_open_after_signature = i
                break

    if first_open_after_signature == -1:
        raise ValueError("Could not find function body opening brace")

    # Now find the matching closing brace for this opening brace
    function_body_start = brace_positions[first_open_after_signature][0]
    brace_count = 1
    function_body_end = -1

    for i in range(first_open_after_signature + 1, len(brace_positions)):
        pos, brace_type = brace_positions[i]
        if brace_type == "open":
            brace_count += 1
        elif brace_type == "close":
            brace_count -= 1
            if brace_count == 0:
                function_body_end = pos
                break

    if function_body_end == -1:
        raise ValueError("Could not find matching function body closing brace")

    # Extract main task function specification (signature + contracts)
    spec_signature = last_fn_content[:function_body_start].strip()
    spec = spec_signature + "\n"

    # Generate stub implementation instead of actual function body
    return_type = parse_return_type(spec_signature)
    default_value = generate_default_value(return_type)

    # Create stub implementation
    stub_body = (
        "{\n    // impl-start\n    assume(false);\n    "
        + default_value
        + "\n    // impl-end\n}"
    )
    code_section = stub_body + "\n"

    # Build helpers section: other functions + proof functions
    helper_parts = []

    # Add other functions (these are helper functions)
    for func in other_functions:
        helper_parts.append(func.strip())

    # Add proof functions
    for proof_fn in proof_functions:
        helper_parts.append(proof_fn.strip())

    helpers_section = "\n\n".join(helper_parts) + "\n" if helper_parts else ""

    # Find the closing verus brace and create postamble
    remaining_after_fn = last_fn_content[function_body_end + 1 :]

    # The postamble should include everything after the last function's closing brace
    # This includes the verus! closing brace and any main function
    # Clean up extra whitespace but preserve structure
    postamble = "\n" + remaining_after_fn.lstrip("\n").rstrip()

    return {
        "vc-description": "",
        "vc-preamble": preamble,
        "vc-helpers": helpers_section,
        "vc-spec": spec,
        "vc-code": code_section,
        "vc-postamble": postamble,
    }


def rust_to_yaml(rust_content: str) -> str:
    """Convert Rust content to YAML format."""
    sections = parse_rust_file(rust_content)

    # Create YAML structure with literal block scalars
    yaml_content = ""
    for key, value in sections.items():
        yaml_content += f"{key}: |-\n"
        if value:
            # Indent each line by 2 spaces
            indented_value = "\n".join(
                "  " + line if line.strip() else "" for line in value.split("\n")
            )
            yaml_content += indented_value.rstrip() + "\n"
        yaml_content += "\n"

    return yaml_content.rstrip()


def convert_file(input_path: Path, output_path: Path) -> None:
    """Convert a single Rust file to YAML format."""
    with open(input_path, "r", encoding="utf-8") as f:
        rust_content = f.read()

    yaml_content = rust_to_yaml(rust_content)

    with open(output_path, "w", encoding="utf-8") as f:
        f.write(yaml_content)

    print(f"Converted {input_path} -> {output_path}")


def main():
    """Main function for command-line usage."""
    parser = argparse.ArgumentParser(
        description="Convert Rust Verus files to YAML format"
    )
    parser.add_argument("input", help="Input Rust file path")
    parser.add_argument(
        "-o",
        "--output",
        help="Output YAML file path (default: input file with .yaml extension)",
    )

    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file {input_path} does not exist")
        return 1

    if args.output:
        output_path = Path(args.output)
    else:
        output_path = input_path.with_suffix(".yaml")

    try:
        convert_file(input_path, output_path)
        return 0
    except Exception as e:
        print(f"Error: {e}")
        return 1


if __name__ == "__main__":
    exit(main())
