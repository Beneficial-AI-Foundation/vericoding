import os
from pathlib import Path
import difflib
from typing import List, Tuple
from datetime import datetime
import re

def remove_comments(content: str) -> str:
    """
    Remove both line comments and block comments from Rust code.
    Preserves empty lines to maintain line numbers for better diff context.
    """
    # First remove block comments (/* ... */)
    # This regex handles nested block comments and preserves newlines
    while True:
        # Find the first /* ... */ block
        block_pattern = r'/\*(?:[^*]|\*(?!/))*\*/'
        match = re.search(block_pattern, content, re.DOTALL)
        if not match:
            break
        
        # Count newlines in the matched block
        newlines = content[match.start():match.end()].count('\n')
        # Replace the block with equivalent number of newlines
        content = content[:match.start()] + '\n' * newlines + content[match.end():]

    # Then remove line comments (//)
    # Process line by line to preserve empty lines
    lines = []
    for line in content.split('\n'):
        # Remove line comment but preserve indentation
        comment_start = line.find('//')
        if comment_start != -1:
            line = line[:comment_start].rstrip()
        lines.append(line)
    
    return '\n'.join(lines)

def find_rust_files(base_dir: str) -> List[Tuple[str, str]]:
    """
    Find all Rust files in the given directory recursively.
    Returns a list of tuples (relative_path, absolute_path).
    """
    results = []
    base_path = Path(base_dir)
    
    for root, _, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.rs'):
                abs_path = os.path.join(root, file)
                rel_path = os.path.relpath(abs_path, base_dir)
                results.append((rel_path, abs_path))
    
    return results

def compare_specs():
    # Define the two directories to compare
    verus_specs_dir = "src/verus_specs"
    verus_specs_no_llm_dir = "src/verus_specs_no_llm"
    
    # Create output directory if it doesn't exist
    output_dir = "diffs"
    os.makedirs(output_dir, exist_ok=True)
    
    # Create output file with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = os.path.join(output_dir, f"specs_comparison_{timestamp}.diff")
    
    # Get all Rust files from both directories
    specs_files = find_rust_files(verus_specs_dir)
    specs_no_llm_files = find_rust_files(verus_specs_no_llm_dir)
    
    # Create dictionaries for easier lookup
    specs_dict = {rel_path: abs_path for rel_path, abs_path in specs_files}
    specs_no_llm_dict = {rel_path: abs_path for rel_path, abs_path in specs_no_llm_files}
    
    # Find common files
    common_files = set(specs_dict.keys()) & set(specs_no_llm_dict.keys())
    
    with open(output_file, 'w') as out_f:
        out_f.write(f"Found {len(common_files)} files with the same name in both directories.\n")
        
        # Compare each common file
        for rel_path in sorted(common_files):
            separator = f"\n{'='*80}\nComparing {rel_path}\n{'='*80}\n"
            out_f.write(separator)
            
            # Read both files
            with open(specs_dict[rel_path], 'r') as f1:
                specs_content = f1.read()
            with open(specs_no_llm_dict[rel_path], 'r') as f2:
                specs_no_llm_content = f2.read()
            
            # Remove comments from both files
            specs_content_no_comments = remove_comments(specs_content)
            specs_no_llm_content_no_comments = remove_comments(specs_no_llm_content)
            
            # Generate diff on the content without comments
            diff = difflib.unified_diff(
                specs_no_llm_content_no_comments.splitlines(keepends=True),
                specs_content_no_comments.splitlines(keepends=True),
                fromfile=f"verus_specs_no_llm/{rel_path}",
                tofile=f"verus_specs/{rel_path}",
                lineterm=''
            )
            
            # Write diff to file
            diff_text = '\n'.join(diff)
            if diff_text:
                out_f.write(diff_text + '\n')
            else:
                out_f.write("Files are identical (ignoring comments)\n")
    
    print(f"Comparison completed. Results written to: {output_file}")

if __name__ == "__main__":
    compare_specs() 