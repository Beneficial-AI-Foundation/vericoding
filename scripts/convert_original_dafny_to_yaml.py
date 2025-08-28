#!/usr/bin/env python3
"""
Convert original HumanEval Dafny files to YAML format.
This will properly split methods and preserve the structure without corrupting postambles.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "benchmarks" / "dafny" / "humaneval"
TARGET_DIR = ROOT / "benchmarks" / "dafny" / "humaneval" / "yaml"


def extract_description_from_lean(task_num: int) -> list[str]:
    """Extract vc-description from corresponding Lean file."""
    lean_dir = ROOT / "benchmarks" / "vericoding_lean" / "humaneval"
    lean_path = lean_dir / f"HumanEval_{task_num}.yaml"
    
    try:
        text = lean_path.read_text(encoding="utf-8")
        lines = text.splitlines()
        in_desc = False
        desc_lines = []
        
        for line in lines:
            if line.startswith("vc-description: |-"):
                in_desc = True
                continue
            if in_desc:
                if line and not line.startswith("  ") and not line == "":
                    break
                if line.strip() not in ["/--", "-/"]:  # Skip comment markers
                    desc_lines.append(line)
        
        return desc_lines
    except Exception:
        return []


def parse_dafny_file(content: str) -> dict:
    """Parse a Dafny file and extract all methods with their sections."""
    lines = content.splitlines()
    
    # Find all method definitions with their names
    methods = []
    for i, line in enumerate(lines):
        match = re.match(r'^\s*method\s+(\w+)', line.strip())
        if match:
            methods.append((i, match.group(1)))
    
    if not methods:
        return {}
    
    # Find boundaries for each method
    method_data = []
    for idx, (start_line, method_name) in enumerate(methods):
        # Find method end (closing brace)
        brace_count = 0
        method_started = False
        end_line = len(lines) - 1
        
        for i in range(start_line, len(lines)):
            line = lines[i]
            if '{' in line:
                method_started = True
                brace_count += line.count('{')
                brace_count -= line.count('}')
            elif method_started:
                brace_count += line.count('{')
                brace_count -= line.count('}')
            
            if method_started and brace_count == 0:
                end_line = i
                break
        
        # Extract method signature (up to opening brace)
        spec_lines = []
        for i in range(start_line, len(lines)):
            line = lines[i]
            if '{' in line:
                brace_pos = line.find('{')
                prefix = line[:brace_pos].rstrip()
                if prefix:
                    spec_lines.append(prefix)
                break
            spec_lines.append(line)
        
        method_data.append({
            'name': method_name,
            'start': start_line,
            'end': end_line,
            'spec': spec_lines
        })
    
    # Find preamble (everything before first method) and postamble (everything after last method)
    first_method_start = methods[0][0] if methods else len(lines)
    last_method_end = method_data[-1]['end'] if method_data else 0
    
    # Preamble: everything before first method
    preamble_lines = []
    for i in range(first_method_start):
        line = lines[i]
        if line.strip() and not line.strip().startswith('// pure-end'):
            preamble_lines.append(line)
    
    # Remove trailing empty lines from preamble
    while preamble_lines and not preamble_lines[-1].strip():
        preamble_lines.pop()
    
    # Postamble: everything after last method
    postamble_lines = []
    if last_method_end + 1 < len(lines):
        for i in range(last_method_end + 1, len(lines)):
            line = lines[i]
            if line.strip():
                postamble_lines.append(line)
    
    return {
        'preamble': preamble_lines,
        'postamble': postamble_lines,
        'methods': method_data,
        'has_method': len(method_data) > 0
    }


def create_method_stubs(methods: list, target_method_idx: int) -> tuple[list[str], list[str]]:
    """Create method stubs for preamble and postamble."""
    preamble_stubs = []
    postamble_stubs = []
    
    for i, method in enumerate(methods):
        if i == target_method_idx:
            continue  # Skip the target method
        
        # Create stub with assume{:axiom} false
        stub_lines = []
        stub_lines.extend(method['spec'])
        stub_lines.append("{")
        stub_lines.append("  assume{:axiom} false;")
        stub_lines.append("}")
        
        if i < target_method_idx:
            preamble_stubs.extend(stub_lines)
            preamble_stubs.append("")  # Empty line between methods
        else:
            postamble_stubs.extend(stub_lines)
            postamble_stubs.append("")  # Empty line between methods
    
    return preamble_stubs, postamble_stubs


def create_yaml_content(dfy_path: Path, sections: dict, method_idx: int = 0) -> str:
    """Create YAML content from parsed sections for a specific method."""
    yaml_lines = []
    
    # Extract task number from filename for description
    stem = dfy_path.stem
    task_num = None
    try:
        if stem.startswith(('000-', '001-', '002-')):  # Handle leading zeros
            task_num = int(stem.split('-')[0])
    except Exception:
        pass
    
    methods = sections.get('methods', [])
    if method_idx >= len(methods):
        return ""
    
    target_method = methods[method_idx]
    method_name = target_method['name']
    
    # vc-description
    desc_lines = []
    if task_num is not None:
        desc_lines = extract_description_from_lean(task_num)
    
    if not desc_lines:
        # Fallback description
        if len(methods) == 1:
            task_name = stem.replace('-', ' ').replace('_', ' ')
            desc_lines = [f"  HumanEval task: {task_name}. Implement according to the specification."]
        else:
            task_name = stem.replace('-', ' ').replace('_', ' ')
            desc_lines = [f"  Auxiliary method '{method_name}' used in HumanEval task: {task_name}."]
    
    yaml_lines.append("vc-description: |-")
    yaml_lines.extend(desc_lines)
    yaml_lines.append("")
    
    # Create method stubs for other methods
    preamble_stubs, postamble_stubs = create_method_stubs(methods, method_idx)
    
    # vc-preamble (original preamble + method stubs before target)
    yaml_lines.append("vc-preamble: |-")
    if sections.get('preamble'):
        for line in sections['preamble']:
            yaml_lines.append(f"  {line}")
        if preamble_stubs:
            yaml_lines.append("")  # Empty line between preamble and stubs
    
    if preamble_stubs:
        for line in preamble_stubs:
            yaml_lines.append(f"  {line}")
    yaml_lines.append("")
    
    # vc-helpers
    yaml_lines.append("vc-helpers: |-")
    yaml_lines.append("")
    
    # vc-spec (target method signature and contracts)
    yaml_lines.append("vc-spec: |-")
    for line in target_method['spec']:
        yaml_lines.append(f"  {line}")
    yaml_lines.append("")
    
    # vc-code
    yaml_lines.append("vc-code: |-")
    yaml_lines.append("  {")
    yaml_lines.append("    assume false;")
    yaml_lines.append("  }")
    yaml_lines.append("")
    
    # vc-postamble (method stubs after target + original postamble)
    yaml_lines.append("vc-postamble: |-")
    if postamble_stubs:
        for line in postamble_stubs:
            yaml_lines.append(f"  {line}")
        if sections.get('postamble'):
            yaml_lines.append("")  # Empty line between stubs and postamble
    
    if sections.get('postamble'):
        for line in sections['postamble']:
            yaml_lines.append(f"  {line}")
    yaml_lines.append("")
    
    return "\n".join(yaml_lines)


def convert_file(dfy_path: Path, output_dir: Path) -> int:
    """Convert a single Dafny file to YAML, creating one file per method."""
    try:
        content = dfy_path.read_text(encoding="utf-8")
        sections = parse_dafny_file(content)
        
        if not sections.get('has_method'):
            return 0
        
        methods = sections.get('methods', [])
        converted_count = 0
        
        for method_idx, method in enumerate(methods):
            yaml_content = create_yaml_content(dfy_path, sections, method_idx)
            if not yaml_content:
                continue
            
            # Create filename based on method count
            if len(methods) == 1:
                output_filename = dfy_path.stem + ".yaml"
            else:
                method_name = method['name']
                output_filename = f"{dfy_path.stem}__{method_name}.yaml"
            
            output_path = output_dir / output_filename
            output_path.write_text(yaml_content, encoding="utf-8")
            converted_count += 1
        
        return converted_count
    except Exception as e:
        print(f"Error converting {dfy_path.name}: {e}")
        return 0


def main() -> None:
    if not SOURCE_DIR.exists():
        print(f"Source directory not found: {SOURCE_DIR}")
        return
    
    TARGET_DIR.mkdir(parents=True, exist_ok=True)
    
    # Clear existing YAML files
    for yaml_file in TARGET_DIR.glob("*.yaml"):
        yaml_file.unlink()
    
    dfy_files = list(SOURCE_DIR.glob("*.dfy"))
    if not dfy_files:
        print(f"No .dfy files found in {SOURCE_DIR}")
        return
    
    print(f"Converting {len(dfy_files)} Dafny files to YAML...")
    
    total_converted = 0
    for dfy_file in sorted(dfy_files):
        converted_count = convert_file(dfy_file, TARGET_DIR)
        total_converted += converted_count
    
    print(f"Successfully converted {len(dfy_files)} Dafny files into {total_converted} YAML files at {TARGET_DIR}")


if __name__ == "__main__":
    main()
