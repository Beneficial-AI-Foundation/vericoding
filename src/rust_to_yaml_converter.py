#!/usr/bin/env python3
"""
Convert Rust Verus files to YAML format following the vericoding template.
"""

import re
import yaml
from pathlib import Path
from typing import Dict, Any
import argparse


def extract_proof_constructs(content: str) -> tuple[str, list[str]]:
    """Extract proof functions and proof blocks from content using balanced brace matching."""
    proof_constructs = []
    
    # Find proof functions and proof blocks
    pos = 0
    while pos < len(content):
        # Look for 'proof fn' or 'proof {'
        proof_fn_match = re.search(r'proof\s+fn\s+', content[pos:])
        proof_block_match = re.search(r'proof\s*\{', content[pos:])
        
        # Find the earliest match
        earliest_match = None
        earliest_pos = float('inf')
        match_type = None
        
        if proof_fn_match and pos + proof_fn_match.start() < earliest_pos:
            earliest_pos = pos + proof_fn_match.start()
            earliest_match = proof_fn_match
            match_type = 'function'
            
        if proof_block_match and pos + proof_block_match.start() < earliest_pos:
            earliest_pos = pos + proof_block_match.start()
            earliest_match = proof_block_match
            match_type = 'block'
        
        if not earliest_match:
            break
            
        # Find the opening brace for both cases
        if match_type == 'function':
            # For proof functions, find the opening brace of the function body
            brace_search_start = pos + proof_fn_match.end()
            brace_match = re.search(r'\{', content[brace_search_start:])
            if not brace_match:
                pos = earliest_pos + 1
                continue
            brace_pos = brace_search_start + brace_match.start()
            construct_start = earliest_pos
        else:
            # For proof blocks, the brace is included in the match
            brace_pos = pos + proof_block_match.end() - 1  # -1 because the match includes the '{'
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
            # Found complete construct
            construct = content[construct_start:search_pos].strip()
            proof_constructs.append(construct)
            pos = search_pos
        else:
            # Unmatched braces, skip this match
            pos = earliest_pos + 1
    
    # Remove all found proof constructs from content
    cleaned_content = content
    for construct in proof_constructs:
        cleaned_content = cleaned_content.replace(construct, '', 1)
    
    # Clean up extra whitespace  
    cleaned_content = re.sub(r'\n\s*\n\s*\n', '\n\n', cleaned_content)
    
    return cleaned_content.strip(), proof_constructs


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
    
    # Extract proof functions/blocks from the remaining content
    remaining_content, proof_constructs = extract_proof_constructs(remaining_content)
    
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
        while last_fn_start > 0 and remaining_content[last_fn_start - 1] in ' \t\n':
            last_fn_start -= 1
        
        # Extract all content before the last function (contains other functions)
        before_last_fn = remaining_content[:last_fn_start].strip()
        if before_last_fn:
            other_functions.append(before_last_fn)
        
        # Process only the last function
        last_fn_content = remaining_content[last_fn_start:]
    else:
        # Single function case
        last_fn_content = remaining_content
    
    # Split the last function between spec and code
    fn_pattern_full = r'(fn\s+\w+.*?)(\{)'
    fn_match = re.search(fn_pattern_full, last_fn_content, re.DOTALL)
    
    if not fn_match:
        raise ValueError("Could not find function declaration")
    
    spec = fn_match.group(1).strip()
    
    # Find the implementation section (everything between braces)
    start_pos = fn_match.end() - 1  # Position of opening brace
    brace_count = 1
    pos = start_pos + 1
    
    while pos < len(last_fn_content) and brace_count > 0:
        if last_fn_content[pos] == '{':
            brace_count += 1
        elif last_fn_content[pos] == '}':
            brace_count -= 1
        pos += 1
    
    if brace_count > 0:
        raise ValueError("Unmatched braces in function")
    
    # Extract function body (between the braces)
    function_body = last_fn_content[start_pos:pos]
    
    # Build code section: function body + other functions + proof constructs
    code_parts = []
    
    # Add the last function's body first
    code_parts.append(function_body.strip())
    
    # Add other functions
    for func in other_functions:
        code_parts.append(func)
    
    # Add proof constructs
    for proof in proof_constructs:
        code_parts.append(proof)
    
    code_section = '\n\n'.join(code_parts) + '\n' if code_parts else '\n'
    
    # Find the closing verus brace and create postamble
    remaining_after_fn = last_fn_content[pos:].strip()
    postamble = "\n" + remaining_after_fn + main_part
    
    return {
        'vc-description': '',
        'vc-preamble': preamble + '\n',
        'vc-helpers': '',
        'vc-spec': spec + '\n', 
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