#!/usr/bin/env python3
"""
Script to remove 'import Imports.AllImports' lines from vc-preamble sections
in all YAML files in the apps_train directory.
"""

import os
from pathlib import Path
from typing import Any, Dict, List, Tuple
import sys
import shutil

# Add src directory to path to import convert_from_yaml
sys.path.append(str(Path(__file__).parent.parent))
from convert_from_yaml import spec_to_yaml

def validate_spec_keys(spec: Dict[str, Any], required_keys: list) -> None:
    """Validate that spec has exactly the same keys as required keys."""
    if spec is None:
        print("Warning: file is empty or invalid YAML")
        return

    spec_keys = set(spec.keys())
    required_keys_set = set(required_keys)
    
    if spec_keys != required_keys_set:
        missing_keys = required_keys_set - spec_keys
        extra_keys = spec_keys - required_keys_set
        
        error_msg = "Key mismatch:"
        if missing_keys:
            error_msg += f" Missing keys: {sorted(missing_keys)}"
        if extra_keys:
            error_msg += f" Extra keys: {sorted(extra_keys)}"
        
        raise ValueError(error_msg)

def check_vc_description(content: str) -> str:
    """Check vc-description for malformed comment blocks and remove empty lines at beginning/end.
    
    Raises an error if:
    - Any line starts with '/*' but is not the first line of the section
    - Any line ends with '*/' but is not the last line of the section
    
    Returns the content with empty lines removed from beginning and end.
    """
    if not content:
        return ""
    
    lines = content.split('\n')
    
    # Remove empty lines at the beginning
    while lines and lines[0].strip() == '':
        lines = lines[1:]
    
    # Remove empty lines at the end
    while lines and lines[-1].strip() == '':
        lines = lines[:-1]

    # Check for lines starting with '/*' that are not the first line
    comment_start = False
    for i, line in enumerate(lines):
        stripped_line = line.lstrip()
        if stripped_line.startswith('/*'):
            if i > 0:
                raise ValueError(f"Line {i+1} starts with '/*' but is not the first line of vc-description")
            elif not line.startswith('/*'):
                raise ValueError(f"Line {i+1} starts with '/*' but there is an unexpected indent")
            else:
                lines[i] = line[2:].lstrip()
                comment_start = True

    # Check for lines ending with '*/' that are not the last line
    comment_end = False
    for i, line in enumerate(lines):
        stripped_line = line.rstrip()
        if stripped_line.endswith('*/'):
            if i < len(lines) - 1:
                raise ValueError(f"Line {i+1} ends with '*/' but is not the last line of vc-description")
            else:
                lines[i] = stripped_line[:-2].rstrip()
                comment_end = True
    
    if (not comment_start and comment_end) or (comment_start and not comment_end):
        raise ValueError("vc-description has a malformed comment block")
    
    return '\n'.join(lines)

def check_for_tag(content: str, key: str, correct_key: str, tag: str, correct_line: str) -> str:
    """
    Remove lines containing the specified tag as a substring.
    Validate that these lines have the correct format and are in the correct section before removal.
    
    Args:
        content: The input string content
        key: The current section key (e.g., "vc-preamble")
        correct_key: The expected section key for this tag (e.g., "vc-spec")
        tag: The tag to look for (e.g., "<vc-spec>" or "</vc-spec>")
        correct_line: The expected line format when stripped (e.g., "-- <vc-spec>")
        
    Returns:
        The content with valid tag lines removed
        
    Raises:
        ValueError: If the tag is found in the wrong section or doesn't match the expected format
    """
    lines = content.splitlines()
    result_lines = []
    
    for line in lines:
        stripped = line.strip()
        
        # Check for the tag
        if tag in line:
            # Check if we're in the correct section
            if correct_key and key != correct_key:
                raise ValueError(f"Tag '{tag}' found in section '{key}' but expected in section '{correct_key}'")
            
            # Check if the line format is correct
            if stripped != correct_line:
                raise ValueError(f"Invalid {tag} line format. Expected '{correct_line}', got: '{line}'")
            
            # Skip this line (don't add to result)
            continue
            
        # Keep all other lines
        result_lines.append(line)
    
    return '\n'.join(result_lines)

def normalize_section_content(content: str) -> str:
    """Normalize section content by removing leading empty lines and reducing consecutive empty lines to one."""
    if not content:
        return ""
    
    lines = content.split('\n')
    
    # Remove empty lines at the start
    while lines and lines[0].strip() == '':
        lines = lines[1:]
    
    # Reduce consecutive empty lines to single empty lines
    normalized_lines = []
    prev_empty = False
    
    for line in lines:
        if line.strip() == '':
            if not prev_empty:
                normalized_lines.append('')
                prev_empty = True
        else:
            normalized_lines.append(line)
            prev_empty = False
    
    # Join and apply rstrip
    return '\n'.join(normalized_lines).rstrip()

def extract_comments_from_content(content: str, multiline_delimiters: List[Tuple[str, str]], monoline_delimiters: List[str]) -> Tuple[str, List[str]]:
    """
    Extract comments from content and return the content without comments plus the extracted comments.
    
    Args:
        content: The input content to process
        multiline_delimiters: List of (start_tag, end_tag) pairs for multiline comments
        monoline_delimiters: List of start_tags for single line comments
    Returns:
        Tuple of (content_without_comments, list_of_extracted_comments)
    """
    if not content:
        return "", []
    
    lines = content.split('\n')
    result_lines = []
    extracted_comments = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped_line = line.lstrip()
        
        # Check for multiline comment start
        multiline_comment_found = False
        for start_tag, end_tag in multiline_delimiters:
            if start_tag in line:
                # Found start of multiline comment (can be in middle of line)
                start_pos = line.find(start_tag)
                
                # Add the part before the start_tag to result_lines
                if start_pos > 0:
                    result_lines.append(line[:start_pos].rstrip())
                
                # Start collecting comment lines with the part including and after start_tag
                current_line = line[start_pos:]
                comment_lines = []
                first_line = True
                
                # Collect all lines until we find the end tag
                while i < len(lines):
                    if not first_line:
                        current_line = lines[i]
                    current_stripped = current_line.strip() 

                    # check for nested multiline comment
                    search_start = len(start_tag) if first_line else 0
                    if start_tag in current_stripped[search_start:]:
                        raise ValueError(f"Nested multiline comment. Found start tag '{start_tag}' in line {i+1}")

                    # add current line to comment lines
                    comment_lines.append(current_line)             

                    # check for end of multiline comment
                    if end_tag in current_stripped:
                        if current_stripped.endswith(end_tag):
                            # Found end of multiline comment
                            break
                        else:
                            raise ValueError(f"Malformed multiline comment. Found end tag '{end_tag}' in line {i+1} but it is not at the end of the line")

                    # advance to next line
                    first_line = False
                    i += 1

                else:
                    # Reached end of content without finding end tag
                    raise ValueError(f"Malformed multiline comment. Reached end of content without finding end tag")
                
                # Join the comment lines and add to extracted comments
                comment_content = '\n'.join(comment_lines).strip()
                if comment_content:
                    extracted_comments.append(comment_content)
                
                multiline_comment_found = True
                break
        
        if not multiline_comment_found:
            # Check for single line comment
            monoline_comment_found = False
            for start_tag in monoline_delimiters:
                if start_tag in line:
                    # Found single line comment
                    start_pos = line.find(start_tag)
                    if start_pos > 0:
                        result_lines.append(line[:start_pos].rstrip())
                    extracted_comments.append(line[start_pos:])
                    monoline_comment_found = True
                    break
            
            if not monoline_comment_found:
                # Not a comment line, keep it
                result_lines.append(line)
        
        i += 1
    
    return '\n'.join(result_lines), extracted_comments

def remove_unnecessary_tags(content: str, unnecessary_tags: List[str]) -> str:
    """
    Remove unnecessary tags from content.
    
    Args:
        content: The input content to process
        unnecessary_tags: List of tag strings to remove (e.g., ['// post-conditions-start', '// post-conditions-end'])
        
    Returns:
        The content with unnecessary tags removed
    """
    if not content or not unnecessary_tags:
        return content
    
    lines = content.split('\n')
    result_lines = []
    
    for line in lines:
        stripped_line = line.strip()
        
        # Check if this line contains any of the unnecessary tags
        should_remove = False
        for tag in unnecessary_tags:
            if tag in line:
                if tag == stripped_line:
                    should_remove = True
                    break
                else:
                    raise ValueError(f"Unnecessary tag '{tag}' found but it is not the whole line")
        
        if not should_remove:
            if stripped_line.startswith("//") and (stripped_line.endswith("start") or stripped_line.endswith("end")):
                raise ValueError(f"New unrecognized tag '{stripped_line}' found")
            else:
                result_lines.append(line)
            
    return '\n'.join(result_lines)

def move_comments_to_description(spec: Dict[str, Any], multiline_delimiters: List[Tuple[str, str]] = None, monoline_delimiters: List[str] = None) -> None:
    """
    Move comments from all fields to the vc-description field.
    
    Args:
        spec: The YAML spec dictionary to modify
        multiline_delimiters: List of (start_tag, end_tag) pairs for multiline comments
        monoline_delimiters: List of start_tags for single line comments
    """
    if multiline_delimiters is None:
        multiline_delimiters = [('/-', '-/'), ('/--', '-/'), ('/-!', '-/')]
    if monoline_delimiters is None:
        monoline_delimiters = ['--']
    
    # Collect all comments from non-description fields
    all_comments = []
    
    for key, value in spec.items():
        if key not in ['vc-description', 'vc-postamble'] and isinstance(value, str):
            content_without_comments, extracted_comments = extract_comments_from_content(
                value, multiline_delimiters, monoline_delimiters
            )
            spec[key] = content_without_comments
            all_comments.extend(extracted_comments)
    
    # Append comments to vc-description
    if all_comments: 
        if 'vc-description' in spec and spec['vc-description']:
            # Add empty line separator if description already has content
            spec['vc-description'] = spec['vc-description'].rstrip() + '\n\n' + '\n\n'.join(all_comments)
        else:
            # Description is empty or doesn't exist, just add comments
            spec['vc-description'] = '\n\n'.join(all_comments)

def check_section_for_sorries(spec: Dict[str, Any], section: str) -> bool:
    """
    Check a section for 'sorry' statements.
    
    Args:
        spec: The YAML spec dictionary to check
        section: The section to check (e.g., 'vc-postamble', 'vc-preamble', 'vc-helpers')
    """
    if section not in spec:
        return True
    if not spec[section]:
        return True
    if spec[section]:
        if 'sorry' in spec[section]:
            return False
        else:
            return True
    
def process_yaml_file(file_path: Path) -> None:
    """Process a single YAML file to remove 'import Imports.AllImports' lines and normalize sections."""

    required_keys = ['vc-description', 'vc-preamble', 'vc-helpers', 
                     'vc-definitions', 'vc-theorems', 'vc-postamble']
                     
    # Import ruamel.yaml here to avoid circular imports
    from ruamel.yaml import YAML
    
    # Read the YAML file with ruamel.yaml to preserve structure
    yaml_loader = YAML()
    yaml_loader.preserve_quotes = True
    
    with open(file_path, 'r', encoding='utf-8') as f:
        spec = yaml_loader.load(f)

    # if 'vc-postamble' in spec and spec['vc-postamble']:
    #     if file_path.parent.parent != Path('benchmarks/lean/fvapps'):
    #         raise ValueError(f"vc-postamble is not empty in {file_path}")

    good_dir = Path('benchmarks/lean/fvapps_bad/yaml_good')
    bad_dir = Path('benchmarks/lean/fvapps_bad/yaml_bad')
    good_dir.mkdir(exist_ok=True)
    bad_dir.mkdir(exist_ok=True)

    # # Move comments from other fields to vc-description
    # move_comments_to_description(spec)

    # # Normalize all sections
    # for key, value in spec.items():
    #     if isinstance(value, str):
    #         spec[key] = normalize_section_content(value)
    
    # # Write back to the file using spec_to_yaml to preserve structure
    # spec_to_yaml(spec, file_path, required_keys)

    # Reopen the file
    with open(file_path, 'r', encoding='utf-8') as f:
        spec = yaml_loader.load(f)

    if check_section_for_sorries(spec, 'vc-postamble') and \
       check_section_for_sorries(spec, 'vc-preamble') and \
       (('vc-helpers' not in spec) or ('vc-helpers' in spec and not spec['vc-helpers'])):
        # print(f"{file_path} has is a good candidate")
        #copy file to benchmarks/lean/fvapps_good/yaml/
        # shutil.copy(file_path, good_dir / file_path.name)
        # print(f"Copied {file_path} to {good_dir / file_path.name}")
        print(f"{file_path} is a good candidate")
    else:
        if not check_section_for_sorries(spec, 'vc-postamble'):
            print(f"{file_path} has sorries in vc-postamble")
        if not check_section_for_sorries(spec, 'vc-preamble'):
            print(f"{file_path} has sorries in vc-preamble")
        if ('vc-helpers' in spec and spec['vc-helpers']):
            print(f"{file_path} has a non-empty vc-helpers")
        # copy file to benchmarks/lean/fvapps_bad/yaml/
        # shutil.copy(file_path, bad_dir / file_path.name)
        # print(f"Copied {file_path} to {bad_dir / file_path.name}")
    

    # ================================================

    # # Check that spec has exactly the same keys as required keys
    # validate_spec_keys(spec, required_keys)
    
    # # Check vc-description for malformed comment blocks and clean up empty lines
    # if 'vc-description' in spec and isinstance(spec['vc-description'], str):
    #     spec['vc-description'] = check_vc_description(spec['vc-description'])
    # else:
    #     raise ValueError(f"vc-description not found in {file_path}")
    
    # # remove tags from all sections
    # for key, value in spec.items():
    #     if isinstance(value, str):
    #         value = check_for_tag(value, key, None, '<vc-spec>', '-- <vc-spec>')
    #         value = check_for_tag(value, key, None, '</vc-spec>', '-- </vc-spec>')
    #         value = check_for_tag(value, key, None, '<vc-code>', '-- <vc-code>')
    #         value = check_for_tag(value, key, None, '<vc-code>', '-- </vc-code>')
    #         value = check_for_tag(value, key, 'vc-definitions', '<vc-definitions>', '-- <vc-definitions>')
    #         value = check_for_tag(value, key, 'vc-definitions', '</vc-definitions>', '-- </vc-definitions>')
    #         value = check_for_tag(value, key, 'vc-theorems', '<vc-theorems>', '-- <vc-theorems>')
    #         value = check_for_tag(value, key, 'vc-theorems', '</vc-theorems>', '-- </vc-theorems>')
    #         value = check_for_tag(value, key, 'vc-helpers', '<vc-helpers>', '-- <vc-helpers>')
    #         value = check_for_tag(value, key, 'vc-helpers', '</vc-helpers>', '-- </vc-helpers>')
    #         value = check_for_tag(value, key, 'vc-preamble', '<vc-preamble>', '-- <vc-preamble>')
    #         value = check_for_tag(value, key, 'vc-preamble', '</vc-preamble>', '-- </vc-preamble>')
    #         value = check_for_tag(value, key, 'vc-postamble', '<vc-postamble>', '-- <vc-postamble>')
    #         value = check_for_tag(value, key, 'vc-postamble', '</vc-postamble>', '-- </vc-postamble>')
    #         value = check_for_tag(value, key, 'vc-description', '<vc-description>', '-- <vc-description>')
    #         value = check_for_tag(value, key, 'vc-description', '</vc-description>', '-- </vc-description>')
    #         spec[key] = value

    # # remove HumanEval tags
    # for key, value in spec.items():
    #     if isinstance(value, str):
    #         value = check_for_tag(value, key, None, '= TASK =', '// ======= TASK =======')
    #         value = check_for_tag(value, key, None, '= SPEC REQUIREMENTS =', '// ======= SPEC REQUIREMENTS =======')
    #         value = check_for_tag(value, key, None, '= HELPERS =', '// ======= HELPERS =======')
    #         value = check_for_tag(value, key, None, '= MAIN METHOD =', '// ======= MAIN METHOD =======')
    #         spec[key] = value

    # if spec['vc-helpers'].strip():
    #     # spec['vc-helpers'] = ""
    #     raise ValueError(f"vc-helpers is not empty")

    # files_with_used_helpers = ["verina_advanced_11_task.yaml", "verina_advanced_13_task.yaml", "verina_advanced_18_task.yaml", "verina_advanced_19_task.yaml", "verina_advanced_1_task.yaml", "verina_advanced_31_task.yaml", "verina_advanced_36_task.yaml", "verina_advanced_45_task.yaml", "verina_advanced_55_task.yaml", "verina_advanced_56_task.yaml", "verina_advanced_59_task.yaml", "verina_advanced_5_task.yaml", "verina_advanced_61_task.yaml", "verina_advanced_67_task.yaml", "verina_advanced_6_task.yaml", "verina_advanced_75_task.yaml", "verina_basic_17_task.yaml", "verina_basic_21_task.yaml", "verina_basic_27_task.yaml", "verina_basic_31_task.yaml", "verina_basic_34_task.yaml", "verina_basic_36_task.yaml", "verina_basic_44_task.yaml", "verina_basic_45_task.yaml", "verina_basic_49_task.yaml", "verina_basic_57_task.yaml", "verina_basic_60_task.yaml", "verina_basic_63_task.yaml", "verina_basic_80_task.yaml"]
    # if spec['vc-helpers'].strip():
    #     if file_path.name in files_with_used_helpers:
    #         spec['vc-preamble'] = spec['vc-preamble']+"\n\n"+spec['vc-helpers']+"\n\n"
    #         print(f"vc-helpers moved to vc-preamble in {file_path.name}")
    #     spec['vc-helpers'] = ""
    #     # raise ValueError(f"vc-helpers is not empty")

    # # Remove unnecessary tags from vc-code    
    # if 'vc-code' in spec and isinstance(spec['vc-code'], str):
    #     unnecessary_tags = [
    #         '// impl-start',
    #         '// impl-end',
    #         '/* impl-start */',
    #         '/* impl-end */',
    #     ]
    #     spec['vc-code'] = remove_unnecessary_tags(spec['vc-code'], unnecessary_tags)

    # if spec['vc-code'].strip():
    #     # Validate vc-code format
    #     vc_code_lines = spec['vc-code'].strip().split('\n')
        
    #     if len(vc_code_lines) not in [3, 4]:
    #         raise ValueError(f"vc-code in {file_path} must have exactly 3 or 4 lines, got {len(vc_code_lines)} \n\n {spec['vc-code']}")
        
    #     # Check first line: should be "{" after stripping
    #     if vc_code_lines[0].strip() != "{":
    #         raise ValueError(f"vc-code in {file_path} first line must be '{{', got: '{vc_code_lines[0]}'")
        
    #     # Check second line: should be "assume{:axiom}false" or "assumefalse" after removing all spaces
    #     second_line_no_spaces = vc_code_lines[1].strip().replace(' ', '')
    #     if second_line_no_spaces not in ["assume(false);"]:
    #         raise ValueError(f"vc-code in {file_path} second line must be 'assume(false);' (ignoring spaces), got: '{vc_code_lines[1]}'")
        
    #     # Check third line: should be "}" after stripping
    #     if vc_code_lines[-1].strip() != "}":
    #         raise ValueError(f"vc-code in {file_path} last line must be '}}', got: '{vc_code_lines[-1]}'")

    # if spec['vc-code'].strip():
    #     spec['vc-code'] = '{\n    assume(false);\n    unreached()\n}\n'
    #     # raise ValueError(f"vc-code is not empty")

    
    # # Remove unnecessary tags from vc-description
    # if 'vc-description' in spec and isinstance(spec['vc-description'], str):
    #     unnecessary_tags = [
    #         '// post-conditions-start',
    #         '// post-conditions-end',
    #         '// pre-conditions-start', 
    #         '// pre-conditions-end',
    #         '// post-condition-start',
    #         '// post-condition-end',
    #         '// pre-condition-start', 
    #         '// pre-condition-end',
    #         '// impl-start',
    #         '// impl-end',
    #         '// pure-end',
    #         '// invariants-start',
    #         '// invariants-end',
    #         '// verus!'
    #     ]
    #     spec['vc-description'] = remove_unnecessary_tags(spec['vc-description'], unnecessary_tags)
    
    # if spec['vc-preamble'] is None:
    #     if "assume(false)" in spec['vc-preamble']:
    #         raise ValueError("assume(false) found in vc-preamble")
    # if spec['vc-spec'] is None:
    #     if "assume(false)" in spec['vc-spec']:
    #         raise ValueError("assume(false) found in vc-spec")

    # # Strip all whitespace from vc-postamble and validate
    # stripped_postamble = ''.join(spec['vc-postamble'].split())
    # if stripped_postamble not in ['fnmain(){}}', '}fnmain(){}']:
    #     raise ValueError(f"vc-postamble has unexpected value: '{spec['vc-postamble']}'")
    
    # Make vc-postamble standard
    # if spec['vc-postamble'].strip():
    #     spec['vc-postamble'] = '}\nfn main() {}\n'
    # else:
    #     raise ValueError(f"vc-postamble is empty")

    # # Normalize all sections
    # for key, value in spec.items():
    #     if isinstance(value, str):
    #         spec[key] = normalize_section_content(value)
    
    # # Write back to the file using spec_to_yaml to preserve structure
    # spec_to_yaml(spec, file_path, required_keys)
    
    # print(f"Processed: {file_path}")

def main():
    """Main function to process all YAML files in directories with yaml subfolders."""
    # Get the language benchmarks directory
    lang_dir = Path('benchmarks/lean')
    
    if not lang_dir.exists():
        print(f"Error: Directory {lang_dir} not found")
        return 1
    
    total_files_processed = 0
    
    # Loop through all immediate folders in the language directory
    # for folder in lang_dir.iterdir():
    for folder in [lang_dir / 'fvapps_bad']:
        if folder.is_dir():
            yaml_subfolder = folder / 'yaml'
            
            # Check if this folder has a yaml subfolder
            if yaml_subfolder.exists() and yaml_subfolder.is_dir():
                print(f"Processing YAML files in {folder.name}/yaml/")
                
                # Find all YAML files in the yaml subfolder
                yaml_files = list(yaml_subfolder.glob('*.yaml'))
                
                if not yaml_files:
                    print(f"  No YAML files found in {yaml_subfolder}")
                    continue
                
                print(f"  Found {len(yaml_files)} YAML files to process")
                
                # Process each file
                count = 0
                # sources_with_errors = []
                for yaml_file in sorted(yaml_files):
                    count += 1
                    if count % 100 == 0:
                        print(f"  Processing {count} of {len(yaml_files)}")
                    try:
                        process_yaml_file(yaml_file)
                        total_files_processed += 1
                    except ValueError as e:
                        # if yaml_file.parent.parent not in sources_with_errors:
                        #     # print(sources_with_errors)
                        #     sources_with_errors.append(yaml_file.parent.parent)
                        print(f"  Validation error in {yaml_file.name}: {e}")
                        # Continue processing other files instead of stopping
                    except Exception as e:
                        print(f"  Error processing {yaml_file.name}: {e}")
                        # Continue processing other files instead of stopping
                
                print(f"  Completed processing {folder.name}/yaml/")
    
    print(f"Processing complete! Total files processed: {total_files_processed}")

if __name__ == "__main__":
    main()
