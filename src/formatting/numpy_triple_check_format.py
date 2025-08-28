#!/usr/bin/env python3
"""
Script to check .lean files for proper formatting according to the vericoding template.

Expected format:
1. Import statements (import and open statements)
2. Description section (/-! ... -/)
3. Implementation (text description followed by def with sorry)
4. Specification (text description followed by theorem with sorry)

Each section should be separated by empty lines, and there should be no empty lines within each section.
"""

import os
import re
import sys
import json
from pathlib import Path

def check_file_format(file_path):
    """Check if a .lean file follows the expected format."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return f"Error reading file: {e}", {}
    
    # Check for the four required components in order
    
    # 1. Check for import statements at the beginning
    if not re.search(r'^import\s+\S+', content, re.MULTILINE):
        return "Missing import statements at the beginning", {}
    
    # 2. Check for description section (/-! ... -/) - OPTIONAL
    desc_match = re.search(r'/-!.*?-/', content, re.DOTALL)
        
    # 3. Check for implementation (def with sorry)
    def_match = re.search(r'/--(?:[^-]|-(?!/))*?-/\s*def\s+\w+[^\n]*(?:[^\n]+\n)*[^\n]*:=\s+sorry', content, re.DOTALL)
    if not def_match:
        return "Missing implementation (def with sorry) or missing comment block before def", {}
    
    # 4. Check for specification (theorem with sorry)
    theorem_match = re.search(r'/--(?:[^-]|-(?!/))*?-/\s*theorem\s+\w+[^\n]*(?:[^\n]+\n)*[^\n]*:=\s+by\s+sorry', content, re.DOTALL)
    if not theorem_match:
        return "Missing specification (theorem with sorry) or missing comment block before theorem", {}
    
    # Check that they appear in the correct order
    def_start = def_match.start()
    theorem_start = theorem_match.start()
    
    if desc_match:
        desc_start = desc_match.start()
        desc_end = desc_match.end()
        if not (desc_start < def_start < theorem_start):
            print(f"desc_start: {desc_start}, def_start: {def_start}, theorem_start: {theorem_start}")
            return "Sections not in correct order: import -> description -> implementation -> specification", {}
        if not (desc_end < def_start):
            return "Description section overlaps with implementation section", {}
        check_start = desc_start
    else:
        if not (def_start < theorem_start):
            return "Sections not in correct order: import -> implementation -> specification", {}
        check_start = def_start
    
    # Extract the import section
    import_section = content[:check_start].strip()

    # Check that def section ends before theorem section starts
    def_end = def_match.end()
    if not (def_end < theorem_start):
        return "Implementation section overlaps with specification section", {}
    
    # Check that there is nothing but whitespace between sections
    if desc_match:
        # Process content between desc_match and def_match line by line
        lines_between_desc_def = content[desc_end:def_start].split('\n')
        open_lines = []
        for i, line in enumerate(lines_between_desc_def):
            line = line.strip()
            if line == '':
                continue  # Empty line is allowed
            elif line.startswith('open '):
                open_lines.append(line)
            else:
                return f"Invalid line between description and implementation at line {i+1}: '{line}'", {}
                # return f"Invalid line between description and implementation at line {i+1}"
        
        # Append open lines to imports section
        if open_lines:
            import_section += '\n' + '\n'.join(open_lines)
    
    content_between_def_theorem = content[def_end:theorem_start].strip()
    if content_between_def_theorem:
        return f"Content found between implementation and specification sections: '{content_between_def_theorem[:100]}...'", {}
        # return f"Content found between implementation and specification sections"

    # Check that every line before the description section (or before def if no description) is either empty or starts with import/open
    lines_before_check = content[:check_start].split('\n')
    for i, line in enumerate(lines_before_check):
        line = line.strip()
        if line and not (line.startswith('import ') or line.startswith('open ')):
            return f"Line {i+1} before description/implementation section is not empty and doesn't start with 'import' or 'open': '{line}'", {}

    # Check that there isn't anything after the end of the theorem section
    theorem_end = theorem_match.end()
    content_after_theorem = content[theorem_end:].strip()
    if content_after_theorem:
        return f"Content found after theorem section: '{content_after_theorem[:100]}...'", {}
        
    # Extract the four sections
    desc_section = desc_match.group(0) if desc_match else ""
    if desc_section:
        desc_lines = desc_section.split('\n')
        if desc_lines[0].strip() != "/-!":
            return f"First line of description section is not '/-!': '{desc_lines[0]}'", {}
        if desc_lines[-1].strip() != "-/":
            return f"Last line of description section is not '-/': '{desc_lines[-1]}'", {}
        # Check that the description section is a valid JSON object
        desc_json = "\n".join(desc_lines[1:-1])
        # replace all "\`" with "`"
        desc_json = desc_json.replace("\\`", "`")
        try:
            json.loads(desc_json)
        except json.JSONDecodeError as e:
            return f"Description section is not a valid JSON object: {e}", {}

    # Split implementation into text and code
    def_match_text = re.search(r'/--(?:[^-]|-(?!/))*?-/', def_match.group(0))
    def_text = def_match_text.group(0) if def_match_text else ""
    def_code = def_match.group(0)[def_match_text.end():].strip() if def_match_text else def_match.group(0)
    
    # Split specification into text and code
    theorem_match_text = re.search(r'/--(?:[^-]|-(?!/))*?-/', theorem_match.group(0))
    theorem_text = theorem_match_text.group(0) if theorem_match_text else ""
    theorem_code = theorem_match.group(0)[theorem_match_text.end():].strip() if theorem_match_text else theorem_match.group(0)
    
    # Split def_code into signature and implementation
    def_parts = def_code.split(':=\n')
    if len(def_parts) != 2:
        return f"def_code does not contain exactly one ':=\n' separator", {}
    def_sig = def_parts[0] + ':=\n'
    def_impl = def_parts[1]
    
    # Split theorem_code into condition and proof
    theorem_parts = theorem_code.split('by\n')
    if len(theorem_parts) != 2:
        return f"theorem_code does not contain exactly one 'by\n' separator", {}
    theorem_cond = theorem_parts[0] + 'by\n'
    theorem_proof = theorem_parts[1]
    
    result = {
        "imports": remove_empty_lines(import_section).rstrip(),
        "description": desc_section.rstrip(),
        "def_text": def_text.rstrip(),
        "def_sig": def_sig.rstrip(),
        "def_impl": def_impl.rstrip(),
        "theorem_text": theorem_text.rstrip(),
        "theorem_cond": theorem_cond.rstrip(),
        "theorem_proof": theorem_proof.rstrip()
    }
    
    # Check for empty lines in def_impl and theorem_proof
    def_lines = def_impl.split('\n')
    for i, line in enumerate(def_lines):
        if line.strip() == '':
            return f"def_impl contains empty line at line {i+1}", {}
    
    theorem_lines = theorem_proof.split('\n')
    for i, line in enumerate(theorem_lines):
        if line.strip() == '':
            return f"theorem_proof contains empty line at line {i+1}", {}
    
    return "ok", result

def remove_empty_lines(text):
    """Remove empty lines from the text."""
    return "\n".join([line for line in text.split('\n') if line.strip() != ''])

def write_yaml_file(result, output_path):
    """Write the JSON result to a YAML file in the specified format."""
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write("vc-description: |-\n")
        print_text = ""
        # if description starts with `/-!` then replace it with `/- `
        description = result["description"]
        if description.startswith("/-!"):
            description = description.replace("/-!", "/- ")
        if description.strip():
            for line in description.split('\n'):
                if not line.strip().startswith('\"code\"'):
                    print_text += "  " + line + "\n"
            if line.strip(): print_text += "\n"
        # if def_text starts with `/--` then replace it with `/- `
        def_text = result["def_text"]
        if def_text.startswith("/--"):
            def_text = def_text.replace("/--", "/- ")
        if def_text.strip():
            for line in def_text.split('\n'):
                print_text += "  " + line + "\n"
            if line.strip(): print_text += "\n"
        # if theorem_text starts with `/--` then replace it with `/- `
        theorem_text = result["theorem_text"]
        if theorem_text.startswith("/--"):
            theorem_text = theorem_text.replace("/--", "/- ")
        if theorem_text.strip():
            for line in theorem_text.split('\n'):
                print_text += "  " + line + "\n"
        if print_text.strip():
            f.write(print_text.rstrip()+"\n\n")
        else:
            f.write("\n")

        f.write("vc-preamble: |-\n")
        if result["imports"].strip():
            for line in result["imports"].split('\n'):
                f.write("  " + line + "\n")
        f.write("\n")
        
        f.write("vc-helpers: |-\n  <vc-helpers>\n  </vc-helpers>\n\n")
        
        f.write("vc-signature: |-\n")
        if result["def_sig"].strip():
            for line in result["def_sig"].split('\n'):
                f.write("  " + line + "\n")
            if line.strip(): f.write("\n")
        else:
            f.write("\n")
        
        f.write("vc-implementation: |-\n  <vc-implementation>\n")
        if result["def_impl"].strip():
            for line in result["def_impl"].split('\n'):
                f.write("  " + line + "\n")
        f.write("  </vc-implementation>\n\n")
        
        f.write("vc-condition: |-\n")
        if result["theorem_cond"].strip():
            for line in result["theorem_cond"].split('\n'):
                f.write("  " + line + "\n")
            if line.strip(): f.write("\n")
        else:
            f.write("\n")
        
        f.write("vc-proof: |-\n  <vc-proof>\n")
        if result["theorem_proof"].strip():
            for line in result["theorem_proof"].split('\n'):
                f.write("  " + line + "\n")
        f.write("  </vc-proof>\n\n")
        
        f.write("vc-postamble: |-\n")

def main():
    """Main function to check all .lean files in the current directory."""
    benchmarks_dir = Path(__file__).parent.parent.parent / "benchmarks"
    numpy_dir = benchmarks_dir / "lean" / "numpy_triple"
    numpy_yaml_dir = benchmarks_dir / "lean" / "numpy_yaml"
    numpy_bad_dir = benchmarks_dir / "lean" / "numpy_bad"
    output_file = benchmarks_dir / "lean" / "wrong_format.txt"   

   
    lean_files = list(numpy_dir.glob('*.lean')) 
    if not lean_files:
        print("No .lean files found in the current directory.")
        return
    
    # Create directories if they don't exist
    numpy_yaml_dir.mkdir(exist_ok=True)
    numpy_bad_dir.mkdir(exist_ok=True)
    
    print(f"Checking {len(lean_files)} .lean files for proper formatting...\n")
    
    wrong_format_files = []
    
    with open(output_file, 'w') as f:
        for file_path in sorted(lean_files):
            status, result = check_file_format(file_path)
            if status != "ok":
                print(f"✗ {file_path.name}: {status}")
                f.write(f"{file_path.name}: {status}\n")
                wrong_format_files.append(file_path.name)
                
                # Copy the file to numpy_bad directory
                bad_file_path = numpy_bad_dir / file_path.name
                import shutil
                shutil.copy2(file_path, bad_file_path)
                print(f"  → Copied to {bad_file_path}")
            else:
                # Write YAML file for files that pass the format check
                yaml_filename = file_path.stem + ".yaml"
                yaml_path = numpy_yaml_dir / yaml_filename
                write_yaml_file(result, yaml_path)
                # print(f"✓ {file_path.name}: Created {yaml_filename}")
            
        print(f"\nSummary:")
        print(f"Total files checked: {len(lean_files)}")
        print(f"Files with correct format: {len(lean_files) - len(wrong_format_files)}")
        print(f"Files with wrong format: {len(wrong_format_files)}")

        f.write(f"\nSummary:")
        f.write(f"Total files checked: {len(lean_files)}\n")
        f.write(f"Files with correct format: {len(lean_files) - len(wrong_format_files)}\n")
        f.write(f"Files with wrong format: {len(wrong_format_files)}\n")
        
        if wrong_format_files:
            # print(f"\nFiles with wrong format:")
            # for file_name in wrong_format_files:
            #     print(f"  - {file_name}")
            
            # Update the wrong_format.txt file
            f.write("Files that DO NOT satisfy the expected format:\n\n")
            for file_name in wrong_format_files:
                f.write(f"- {file_name}\n")
            
            print(f"\nUpdated {output_file}")
        else:
            print("\nAll files have the correct format!")
        
if __name__ == "__main__":
    main()
