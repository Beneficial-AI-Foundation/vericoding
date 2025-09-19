#!/usr/bin/env python3
"""
Script to process fvapps YAML files and move guard_msgs and eval patterns
from vc-theorems to vc-postamble, uncommenting them in the process.
"""

import os
import re
from pathlib import Path
from ruamel.yaml import YAML
from typing import Dict, Any, List, Tuple


def find_guard_msgs_patterns(content: str) -> List[Tuple[str, int, int]]:
    """
    Find all guard_msgs and eval patterns in the content.
    Returns a list of tuples: (pattern_text, start_pos, end_pos)
    """
    patterns = []
    
    # Pattern to match the full block:
    # /-
    #   info: [some value] or info: some_value
    # -/
    # -- #guard_msgs in
    # -- #eval some_expression
    pattern = re.compile(
        r'(/-.*?info:\s*(?:\[.*?\]|[^\n]+).*?-/\s*--\s*#guard_msgs in\s*--\s*#eval.*?)(?=\n|$)',
        re.DOTALL | re.MULTILINE
    )
    
    for match in pattern.finditer(content):
        patterns.append((match.group(1), match.start(), match.end()))
    
    return patterns


def uncomment_guard_msgs(pattern: str) -> str:
    """
    Uncomment the #guard_msgs and #eval lines in the pattern.
    """
    # Replace commented lines with uncommented versions
    uncommented = re.sub(r'--\s*#guard_msgs in', '#guard_msgs in', pattern)
    uncommented = re.sub(r'--\s*#eval', '#eval', uncommented)
    return uncommented


def process_yaml_file(file_path: Path) -> bool:
    """
    Process a single YAML file to move guard_msgs patterns from vc-theorems to vc-postamble.
    Returns True if the file was modified, False otherwise.
    """
    yaml = YAML()
    yaml.preserve_quotes = True
    yaml.width = 1000  # Prevent line wrapping
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            data = yaml.load(f)
    except Exception as e:
        print(f"Error loading {file_path}: {e}")
        return False
    
    if not isinstance(data, dict):
        return False
    
    # Check if vc-theorems exists and has content
    if 'vc-theorems' not in data or not data['vc-theorems']:
        return False
    
    theorems_content = data['vc-theorems']
    patterns = find_guard_msgs_patterns(theorems_content)
    
    if not patterns:
        return False
    
    # Remove patterns from vc-theorems
    new_theorems = theorems_content
    for pattern, start, end in reversed(patterns):  # Reverse to maintain positions
        new_theorems = new_theorems[:start] + new_theorems[end:]
    
    # Clean up extra whitespace
    new_theorems = re.sub(r'\n\s*\n\s*\n', '\n\n', new_theorems).strip()
    
    # Add patterns to vc-postamble (uncommented)
    if 'vc-postamble' not in data:
        data['vc-postamble'] = ""
    
    postamble_content = data['vc-postamble']
    
    # Add uncommented patterns to postamble
    for pattern, _, _ in patterns:
        uncommented_pattern = uncomment_guard_msgs(pattern)
        if postamble_content.strip():
            postamble_content += "\n\n" + uncommented_pattern
        else:
            postamble_content = uncommented_pattern
    
    # Update the data
    data['vc-theorems'] = new_theorems
    data['vc-postamble'] = postamble_content
    
    # Write back to file
    try:
        with open(file_path, 'w', encoding='utf-8') as f:
            yaml.dump(data, f)
        return True
    except Exception as e:
        print(f"Error writing {file_path}: {e}")
        return False


def main():
    """Main function to process all YAML files in the fvapps directory."""
    fvapps_dir = Path("benchmarks/lean/fvapps/yaml")
    
    if not fvapps_dir.exists():
        print(f"Directory {fvapps_dir} does not exist!")
        return
    
    yaml_files = list(fvapps_dir.glob("*.yaml"))
    print(f"Found {len(yaml_files)} YAML files to process...")
    
    processed_count = 0
    error_count = 0
    
    for yaml_file in yaml_files:
        try:
            if process_yaml_file(yaml_file):
                processed_count += 1
                print(f"Processed: {yaml_file.name}")
        except Exception as e:
            error_count += 1
            print(f"Error processing {yaml_file.name}: {e}")
    
    print(f"\nProcessing complete!")
    print(f"Files processed: {processed_count}")
    print(f"Errors: {error_count}")


if __name__ == "__main__":
    main()