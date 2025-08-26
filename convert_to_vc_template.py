#!/usr/bin/env python3
"""
Simple script to convert Dafny files to the new vc-template format.
"""

import os
import glob
import re

def needs_conversion(content: str) -> bool:
    """Check if a file needs conversion to the new template format."""
    # Check if file has the complete template structure
    has_vc_spec_open = '// <vc-spec>' in content
    has_vc_spec_close = '// </vc-spec>' in content
    has_vc_code_open = '// <vc-code>' in content
    has_vc_code_close = '// </vc-code>' in content
    has_vc_helpers_open = '// <vc-helpers>' in content
    has_vc_helpers_close = '// </vc-helpers>' in content
    
    # Check for malformed templates (duplicate tags, wrong nesting, etc.)
    vc_spec_count = content.count('// <vc-spec>')
    vc_spec_close_count = content.count('// </vc-spec>')
    vc_code_count = content.count('// <vc-code>')
    vc_code_close_count = content.count('// </vc-code>')
    vc_helpers_count = content.count('// <vc-helpers>')
    vc_helpers_close_count = content.count('// </vc-helpers>')
    
    # File needs conversion if:
    # 1. Any required tags are missing, OR
    # 2. There are duplicate tags (count > 1), OR
    # 3. Tags are not properly paired
    has_all_tags = (has_vc_spec_open and has_vc_spec_close and 
                    has_vc_code_open and has_vc_code_close and 
                    has_vc_helpers_open and has_vc_helpers_close)
    
    has_duplicates = (vc_spec_count > 1 or vc_spec_close_count > 1 or
                     vc_code_count > 1 or vc_code_close_count > 1 or
                     vc_helpers_count > 1 or vc_helpers_close_count > 1)
    
    tags_not_paired = (vc_spec_count != vc_spec_close_count or
                       vc_code_count != vc_code_close_count or
                       vc_helpers_count != vc_helpers_close_count)
    
    return not has_all_tags or has_duplicates or tags_not_paired

def convert_to_vc_template(content: str) -> str:
    """Convert a Dafny file to the new vc-template format."""
    lines = content.split('\n')
    
    # Find the main method/function (usually the last one with requires/ensures)
    main_start = -1
    main_end = -1
    
    for i, line in enumerate(lines):
        if re.match(r'\s*(method|function|lemma|predicate)\s+\w+', line.strip()):
            main_start = i
            # Find the end of this method
            brace_count = 0
            in_method = False
            for j in range(i, len(lines)):
                if '{' in lines[j]:
                    if not in_method:
                        in_method = True
                    brace_count += 1
                if '}' in lines[j]:
                    brace_count -= 1
                    if brace_count == 0 and in_method:
                        main_end = j
                        break
    
    if main_start == -1:
        # No method found, just add empty template
        return content + '\n\n// <vc-helpers>\n// </vc-helpers>\n\n// <vc-spec>\n// </vc-spec>\n// <vc-code>\n// </vc-code>'
    
    # Build new content
    new_lines = []
    
    # Add everything before the main method
    new_lines.extend(lines[:main_start])
    
    # Add vc-helpers section
    new_lines.append('// <vc-helpers>')
    new_lines.append('// </vc-helpers>')
    new_lines.append('')
    
    # Add vc-spec section (method signature + opening brace)
    new_lines.append('// <vc-spec>')
    
    # Find where method body starts (opening brace)
    brace_line = -1
    for i in range(main_start, main_end + 1):
        if '{' in lines[i]:
            brace_line = i
            break
    
    if brace_line == -1:
        brace_line = main_end
    
    # Add method signature and opening brace
    for i in range(main_start, brace_line + 1):
        new_lines.append(lines[i])
    
    new_lines.append('// </vc-spec>')
    
    # Add vc-code section
    new_lines.append('// <vc-code>')
    new_lines.append('  assume false;')
    new_lines.append('}')
    new_lines.append('// </vc-code>')
    
    # Add everything after the main method
    new_lines.extend(lines[main_end + 1:])
    
    return '\n'.join(new_lines)

def process_file(file_path: str) -> bool:
    """Process a single Dafny file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if not needs_conversion(content):
            print(f"✓ {os.path.basename(file_path)} - Already converted")
            return False
        
        # Convert the file
        new_content = convert_to_vc_template(content)
        
        # Write back to file
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        print(f"✓ {os.path.basename(file_path)} - Converted")
        return True
        
    except Exception as e:
        print(f"✗ {os.path.basename(file_path)} - Error: {e}")
        return False

def main():
    """Main function to convert all Dafny files."""
    dafnybench_dir = "benchmarks/vericoding_dafny/dafnybench"
    
    if not os.path.exists(dafnybench_dir):
        print(f"Error: Directory {dafnybench_dir} not found!")
        return
    
    # Find all .dfy files
    dfy_files = glob.glob(os.path.join(dafnybench_dir, "*.dfy"))
    
    if not dfy_files:
        print("No .dfy files found!")
        return
    
    print(f"Found {len(dfy_files)} .dfy files")
    print("Converting files to new vc-template format...")
    print("-" * 50)
    
    converted_count = 0
    already_converted_count = 0
    
    for file_path in dfy_files:
        if process_file(file_path):
            converted_count += 1
        else:
            already_converted_count += 1
    
    print("-" * 50)
    print(f"Summary:")
    print(f"  - Files converted: {converted_count}")
    print(f"  - Files already converted: {already_converted_count}")
    print(f"  - Total files: {len(dfy_files)}")

if __name__ == "__main__":
    main()
