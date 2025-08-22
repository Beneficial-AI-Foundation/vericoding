#!/usr/bin/env python3
"""
Convert Rust Verus files to YAML format following the vericoding template.
"""

import re
import yaml
from pathlib import Path
from typing import Dict, Any
import argparse


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
    
    # Find function signature and ensures clause (spec section)
    # Look for fn declaration up to the opening brace
    fn_pattern = r'(fn\s+\w+.*?)(\{)'
    fn_match = re.search(fn_pattern, remaining_content, re.DOTALL)
    
    if not fn_match:
        raise ValueError("Could not find function declaration")
    
    spec = fn_match.group(1).strip()
    
    # Find the implementation section (everything between braces)
    # Find the matching closing brace for the function
    start_pos = fn_match.end() - 1  # Position of opening brace
    brace_count = 1
    pos = start_pos + 1
    
    while pos < len(remaining_content) and brace_count > 0:
        if remaining_content[pos] == '{':
            brace_count += 1
        elif remaining_content[pos] == '}':
            brace_count -= 1
        pos += 1
    
    if brace_count > 0:
        raise ValueError("Unmatched braces in function")
    
    # Extract function body (between the braces)
    function_body = remaining_content[start_pos:pos]
    
    # Find the closing verus brace
    remaining_after_fn = remaining_content[pos:].strip()
    postamble = "\n" + remaining_after_fn + main_part
    
    return {
        'vc-description': '',
        'vc-preamble': preamble + '\n',
        'vc-helpers': '',
        'vc-spec': spec + '\n',
        'vc-code': function_body + '\n',
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