#!/usr/bin/env python3
"""
Convert Rust Verus files to YAML format following the vericoding template.
"""

import re
import yaml
from pathlib import Path
from typing import Dict, Any
import argparse


def extract_proof_and_spec_functions(content: str) -> tuple[str, list[str], list[str]]:
    """Extract proof functions and spec functions from content, leave proof blocks inside functions."""
    proof_functions = []
    spec_functions = []
    
    # Find proof functions and spec functions (not proof blocks)
    pos = 0
    while pos < len(content):
        # Look for 'proof fn' or 'spec fn'
        proof_fn_match = re.search(r'proof\s+fn\s+', content[pos:])
        spec_fn_match = re.search(r'spec\s+fn\s+', content[pos:])
        
        # Find the earliest match
        earliest_match = None
        earliest_pos = float('inf')
        match_type = None
        
        if proof_fn_match and pos + proof_fn_match.start() < earliest_pos:
            earliest_pos = pos + proof_fn_match.start()
            earliest_match = proof_fn_match
            match_type = 'proof'
            
        if spec_fn_match and pos + spec_fn_match.start() < earliest_pos:
            earliest_pos = pos + spec_fn_match.start()
            earliest_match = spec_fn_match
            match_type = 'spec'
        
        if not earliest_match:
            break
            
        # Find the opening brace of the function body
        brace_search_start = pos + earliest_match.end()
        brace_match = re.search(r'\{', content[brace_search_start:])
        if not brace_match:
            pos = pos + earliest_match.end()
            continue
            
        brace_pos = brace_search_start + brace_match.start()
        construct_start = earliest_pos
        
        # Find the matching closing brace
        brace_count = 1
        search_pos = brace_pos + 1
        
        while search_pos < len(content) and brace_count > 0:
            if content[search_pos] == '{':
                brace_count += 1
            elif content[search_pos] == '}':
                brace_count -= 1
            search_pos += 1
            
        if brace_count == 0:
            # Found complete proof function
            construct = content[construct_start:search_pos]
            # Clean up indentation while preserving structure
            lines = construct.split('\n')
            if lines:
                # Find minimum indentation (excluding empty lines)
                min_indent = float('inf')
                for line in lines:
                    if line.strip():  # Skip empty lines
                        indent = len(line) - len(line.lstrip())
                        min_indent = min(min_indent, indent)
                
                # Remove common indentation from all lines
                if min_indent != float('inf'):
                    cleaned_lines = []
                    for line in lines:
                        if line.strip():  # Non-empty line
                            cleaned_lines.append(line[min_indent:] if len(line) >= min_indent else line.lstrip())
                        else:  # Empty line
                            cleaned_lines.append('')
                    construct = '\n'.join(cleaned_lines).strip()
            
            if match_type == 'proof':
                proof_functions.append(construct)
            else:  # match_type == 'spec'
                spec_functions.append(construct)
            pos = search_pos
        else:
            # Unmatched braces, skip this match
            pos = pos + earliest_match.end()
    
    # Remove all found proof and spec functions from content
    cleaned_content = content
    for construct in proof_functions + spec_functions:
        cleaned_content = cleaned_content.replace(construct, '', 1)
    
    # Clean up extra whitespace  
    cleaned_content = re.sub(r'\n\s*\n\s*\n', '\n\n', cleaned_content)
    
    return cleaned_content.strip(), proof_functions, spec_functions


def parse_rust_file(content: str) -> Dict[str, str]:
    """Parse a Rust file and extract the different sections for YAML conversion."""
    
    # Remove the final "fn main() {}" line for processing
    content = content.rstrip()
    main_pattern = r'\nfn main\(\) \{\}$'
    main_match = re.search(main_pattern, content)
    main_part = ""
    if main_match:
        main_part = main_match.group(0)
        content = content[:main_match.start()]
    
    # Extract imports and opening verus block (preamble)
    preamble_pattern = r'^(.*?verus!\s*\{)\s*'
    preamble_match = re.match(preamble_pattern, content, re.DOTALL)
    
    if not preamble_match:
        raise ValueError("Could not find verus! block opening")
    
    preamble = preamble_match.group(1) + "\n"
    remaining_content = content[preamble_match.end():]
    
    # Extract proof functions and spec functions (not proof blocks) from the remaining content
    remaining_content, proof_functions, spec_functions = extract_proof_and_spec_functions(remaining_content)
    
    # Find all normal function declarations (excluding main)
    fn_pattern = r'fn\s+(?!main\b)\w+'
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
        lines_before = remaining_content[:last_fn_start].split('\n')
        
        # Go backwards through lines to find where the function really starts
        function_start_line_idx = len(lines_before) - 1
        
        # Skip empty lines and find the last non-empty line before the function
        while function_start_line_idx >= 0 and not lines_before[function_start_line_idx].strip():
            function_start_line_idx -= 1
        
        # Check if there are attributes or comments that belong to this function
        while function_start_line_idx >= 0:
            line = lines_before[function_start_line_idx].strip()
            # If this line is an attribute, comment, or empty line that should be included
            if (line.startswith('#[') or 
                line.startswith('//') or 
                not line):
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
            last_fn_start = len('\n'.join(lines_before[:function_start_line_idx + 1]))
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
    
    # Split the last function between spec and code by finding the function body braces
    fn_start = re.search(r'fn\s+\w+', last_fn_content)
    if not fn_start:
        raise ValueError("Could not find function declaration")
    
    # Find all braces and match them properly from the function start
    # Look for patterns that indicate the end of function signature/specs
    function_body_start = -1
    function_body_end = -1
    
    # Look for specific patterns that mark the end of specifications
    # The function body typically starts after "// post-conditions-end" or similar
    spec_end_patterns = [
        r'//\s*post-conditions-end',
        r'//\s*ensures-end', 
        r'//\s*spec-end'
    ]
    
    spec_end_pos = -1
    for pattern in spec_end_patterns:
        match = re.search(pattern, last_fn_content)
        if match:
            spec_end_pos = match.end()
            break
    
    # If we found a spec end pattern, look for the next opening brace
    if spec_end_pos != -1:
        for i in range(spec_end_pos, len(last_fn_content)):
            if last_fn_content[i] == '{':
                function_body_start = i
                break
    
    # Fallback: if no spec end pattern found, find the last opening brace before function content
    if function_body_start == -1:
        # Count braces and find the outermost opening brace for the function
        brace_positions = []
        for i in range(fn_start.end(), len(last_fn_content)):
            if last_fn_content[i] == '{':
                brace_positions.append(i)
        
        if brace_positions:
            # Try the last opening brace (most likely to be the function body)
            function_body_start = brace_positions[-1]
    
    if function_body_start == -1:
        raise ValueError("Could not find function body opening brace")
    
    # Now find the matching closing brace by counting from the opening brace
    brace_count = 1
    for i in range(function_body_start + 1, len(last_fn_content)):
        char = last_fn_content[i]
        if char == '{':
            brace_count += 1
        elif char == '}':
            brace_count -= 1
            if brace_count == 0:
                function_body_end = i
                break
    
    if function_body_end == -1:
        raise ValueError("Could not find matching function body closing brace")
    
    spec_signature = last_fn_content[:function_body_start].strip()
    
    # Combine spec functions (at start) + function signature
    spec_parts = []
    for spec_fn in spec_functions:
        spec_parts.append(spec_fn)
    spec_parts.append(spec_signature)
    spec = '\n\n'.join(spec_parts) + '\n' if spec_parts else spec_signature + '\n'
    
    # Extract function body (between the braces we already found)
    function_body = last_fn_content[function_body_start:function_body_end + 1]
    
    # Build code section: function body + other functions + proof functions
    code_parts = []
    
    # Add the last function's body first
    code_parts.append(function_body.strip())
    
    # Add other functions
    for func in other_functions:
        code_parts.append(func)
    
    # Add proof functions (proof blocks stay inside functions)
    for proof_fn in proof_functions:
        code_parts.append(proof_fn)
    
    code_section = '\n\n'.join(code_parts) + '\n' if code_parts else '\n'
    
    # Find the closing verus brace and create postamble
    remaining_after_fn = last_fn_content[function_body_end + 1:].strip()
    postamble = "\n" + remaining_after_fn + main_part
    
    return {
        'vc-description': '',
        'vc-preamble': preamble + '\n',
        'vc-helpers': '',
        'vc-spec': spec, 
        'vc-code': code_section,
        'vc-postamble': postamble
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
            indented_value = '\n'.join('  ' + line if line.strip() else '' for line in value.split('\n'))
            yaml_content += indented_value.rstrip() + "\n"
        yaml_content += "\n"
    
    return yaml_content.rstrip()


def convert_file(input_path: Path, output_path: Path) -> None:
    """Convert a single Rust file to YAML format."""
    with open(input_path, 'r', encoding='utf-8') as f:
        rust_content = f.read()
    
    yaml_content = rust_to_yaml(rust_content)
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(yaml_content)
    
    print(f"Converted {input_path} -> {output_path}")


def main():
    """Main function for command-line usage."""
    parser = argparse.ArgumentParser(description="Convert Rust Verus files to YAML format")
    parser.add_argument("input", help="Input Rust file path")
    parser.add_argument("-o", "--output", help="Output YAML file path (default: input file with .yaml extension)")
    
    args = parser.parse_args()
    
    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: Input file {input_path} does not exist")
        return 1
    
    if args.output:
        output_path = Path(args.output)
    else:
        output_path = input_path.with_suffix('.yaml')
    
    try:
        convert_file(input_path, output_path)
        return 0
    except Exception as e:
        print(f"Error: {e}")
        return 1


if __name__ == "__main__":
    exit(main())