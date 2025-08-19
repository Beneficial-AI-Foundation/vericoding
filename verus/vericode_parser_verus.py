#!/usr/bin/env python3
"""
Vericode Parser Module for Verus
Handles parsing, extraction, and manipulation of Verus code blocks.
"""

import os
import re
import subprocess

def find_verus_files(directory):
    """Find all .rs files in a directory that contain Verus code."""
    try:
        verus_files = []
        for root, dirs, files in os.walk(directory):
            # Skip debug directories and generated directories
            dirs[:] = [d for d in dirs if not (d.startswith('debug') or 
                                              d.startswith('vericoding_on_') or
                                              d.startswith('generated') or
                                              d.startswith('impl_'))]
            
            for f in files:
                if f.endswith(".rs") and not f.startswith("impl_"):
                    file_path = os.path.join(root, f)
                    try:
                        with open(file_path, 'r', encoding='utf-8') as file:
                            content = file.read()
                            # Check if it contains Verus-specific patterns
                            if ('verus!' in content or 
                                'spec fn' in content or 
                                'proof fn' in content or
                                'ensures' in content or
                                'requires' in content):
                                verus_files.append(file_path)
                    except Exception as e:
                        print(f"Error reading file {file_path}: {e}")
                        continue
        return verus_files
    except Exception as e:
        print(f"Error reading directory {directory}: {e}")
        return []

def extract_verus_code(output):
    """Extract Verus code from LLM response."""
    # First try to extract from code blocks
    code_block_match = re.search(r'```rust\n(.*?)```', output, re.DOTALL | re.IGNORECASE)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(code)
        return code
    
    # If no rust code block, try to find any code block
    code_pattern = r'```\s*\n(.*?)\n```'
    match = re.search(code_pattern, output, re.DOTALL)
    
    if match:
        code = match.group(1).strip()
        code = fix_incomplete_code(code)
        return code
    
    # If no code blocks found, try to extract lines that look like Verus code
    lines = output.split('\n')
    verus_lines = []
    in_code_section = False
    
    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (line.strip().startswith('Looking at') or
            line.strip().startswith('The errors show that:') or
            line.strip().startswith('The issue is in') or
            line.strip().startswith('This function will be') or
            line.strip().startswith('Below is a Verus program') or
            line.strip().startswith('// This function will be') or
            line.strip().startswith('// Below is a Verus program') or
            line.strip().startswith('```') or
            line.strip().startswith('1.') or
            line.strip().startswith('2.') or
            line.strip().startswith('3.') or
            line.strip().startswith('4.') or
            line.strip().startswith('5.')):
            continue
        
        # Start collecting when we see Verus keywords
        if (line.find('fn ') != -1 or 
            line.find('spec fn ') != -1 or 
            line.find('proof fn ') != -1 or
            line.find('verus!') != -1 or
            line.find('ensures') != -1 or
            line.find('requires') != -1 or
            line.find('use vstd::') != -1 or
            line.find('return ') != -1 or
            line.find('let ') != -1 or
            line.find('if ') != -1 or
            line.find('for ') != -1 or
            line.find('while ') != -1 or
            line.strip().startswith('//') or
            line.strip().startswith('/*') or
            line.strip().startswith('*/')):
            in_code = True
        
        if in_code:
            verus_lines.append(line)
    
    if verus_lines:
        code = '\n'.join(verus_lines).strip()
        code = fix_incomplete_code(code)
        return code
    
    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(code)
    return code

def fix_incomplete_code(code):
    """Fix common incomplete code patterns in Verus."""
    lines = code.split('\n')
    fixed_lines = []
    
    for i, line in enumerate(lines):
        # Fix incomplete string literals
        if '= "' in line and '";' not in line:
            if line.strip().endswith('= "') or line.strip().endswith('= ""'):
                line = re.sub(r'= ""?$', '= "";', line)
            elif line.strip().endswith('"'):
                line = line + ';'
        
        # Fix incomplete variable declarations
        if 'let ' in line and ' = ' in line and not line.endswith(';'):
            if line.strip().endswith('= ""'):
                line = line + ';'
            elif line.strip().endswith('= "') or line.strip().endswith('='):
                line = re.sub(r'= ""?$', '= "";', line)
        
        # Fix incomplete function bodies
        if line.strip().startswith('fn ') and '{' not in line:
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('fn ') or lines[j].strip().startswith('spec fn '):
                    break
            if not has_body:
                line = line + '\n{\n    // TODO: Implement function body\n}'
        
        # Fix incomplete spec function bodies
        if line.strip().startswith('spec fn ') and '{' not in line:
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('fn ') or lines[j].strip().startswith('spec fn '):
                    break
            if not has_body:
                line = line + '\n{\n    // TODO: Implement spec function body\n}'
        
        # Fix incomplete proof function bodies
        if line.strip().startswith('proof fn ') and '{' not in line:
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('fn ') or lines[j].strip().startswith('proof fn '):
                    break
            if not has_body:
                line = line + '\n{\n    // TODO: Implement proof function body\n}'
        
        fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def extract_impl_blocks(code):
    """Extract implementation blocks from Verus code."""
    # Look for function implementations within verus! blocks
    pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_spec_blocks(code):
    """Extract functions with default return values that need implementation."""
    # Very simple approach: just look for the specific patterns we know exist
    target_functions = []
    
    # Look for functions with "return false;" (most common pattern)
    false_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*return\s+false;[^{}]*\}'
    false_matches = re.findall(false_pattern, code, re.DOTALL)
    target_functions.extend(false_matches)
    
    # Look for functions with "return true;"
    true_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*return\s+true;[^{}]*\}'
    true_matches = re.findall(true_pattern, code, re.DOTALL)
    target_functions.extend(true_matches)
    
    # Look for functions with "return 0;"
    zero_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*return\s+0;[^{}]*\}'
    zero_matches = re.findall(zero_pattern, code, re.DOTALL)
    target_functions.extend(zero_matches)
    
    # Look for functions with "return 1;"
    one_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*return\s+1;[^{}]*\}'
    one_matches = re.findall(one_pattern, code, re.DOTALL)
    target_functions.extend(one_matches)
    
    # Look for functions with TODO comments
    todo_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*TODO[^{}]*\}'
    todo_matches = re.findall(todo_pattern, code, re.DOTALL | re.IGNORECASE)
    target_functions.extend(todo_matches)
    
    # Remove duplicates
    return list(set(target_functions))

def extract_todo_blocks(code):
    """Extract functions with default return values or TODO comments that need implementation."""
    # Use the same approach as extract_spec_blocks
    return extract_spec_blocks(code)

def extract_specification(code_block):
    """Extract the specification part (signature + ensures + requires) from a code block."""
    lines = code_block.split('\n')
    spec_lines = []
    in_body = False
    
    for line in lines:
        stripped = line.strip()
        
        # Stop when we hit the body
        if stripped == '{':
            in_body = True
            break
        
        # Include the line if it's part of the specification
        if not in_body:
            spec_lines.append(line)
    
    spec = '\n'.join(spec_lines).strip()
    
    # Remove trailing empty braces {} that don't affect the specification
    spec = re.sub(r'\s*\{\s*\}\s*$', '', spec)
    
    return spec

def normalize_specification(spec):
    """Normalize specification by removing comments and extra whitespace for comparison."""
    if not spec:
        return ""
    
    lines = spec.split('\n')
    normalized_lines = []
    
    for line in lines:
        stripped = line.strip()
        
        # Skip comment lines (lines starting with //)
        if stripped.startswith('//'):
            continue
            
        # Remove inline comments (everything after // on the same line)
        if '//' in stripped:
            stripped = stripped.split('//')[0].strip()
            
        # Only add non-empty lines
        if stripped:
            normalized_lines.append(stripped)
    
    # Join and normalize whitespace
    normalized = ' '.join(normalized_lines)
    # Remove extra whitespace
    normalized = re.sub(r'\s+', ' ', normalized).strip()
    
    return normalized

def extract_body(code_block):
    """Extract the body part from a code block."""
    lines = code_block.split('\n')
    body_lines = []
    in_body = False
    brace_count = 0
    
    for line in lines:
        stripped = line.strip()
        if stripped == '{':
            in_body = True
            brace_count += 1
            body_lines.append(line)
        elif in_body:
            body_lines.append(line)
            if stripped == '{':
                brace_count += 1
            elif stripped == '}':
                brace_count -= 1
                if brace_count == 0:
                    break
    
    return '\n'.join(body_lines).strip()

def get_signature(code_block):
    """Extract function signature from code block."""
    lines = code_block.split('\n')
    for line in lines:
        # Strip leading whitespace before checking for keywords
        stripped = line.strip()
        if any(keyword in stripped for keyword in ['fn ', 'spec fn ', 'proof fn ']):
            # Return the line up to the first { or ensures/requires
            signature = stripped.split('{')[0].split('ensures')[0].split('requires')[0].strip()
            return signature
    return None

def merge_spec_with_body(original_spec, generated_body):
    """Merge original specification with generated body."""
    if not original_spec or not generated_body:
        return None
    
    # Combine spec and body
    return original_spec + '\n' + generated_body

def count_todos_and_specs(code):
    """Count the number of TODO comments and spec functions in the code."""
    lines = code.split('\n')
    nr_todos = 0
    nr_spec = 0
    
    for line in lines:
        stripped_line = line.strip()
        # Count TODO comments
        if 'TODO' in stripped_line.upper():
            nr_todos += 1
        # Count spec functions
        if stripped_line.startswith('spec fn ') or stripped_line.startswith('proof fn '):
            nr_spec += 1
    
    return nr_todos, nr_spec

def detect_compilation_errors(output):
    """Detect if the output contains compilation errors."""
    compilation_error_indicators = [
        "error:",
        "failed to compile",
        "type error",
        "compilation error",
        "syntax error",
        "cannot resolve",
        "unresolved identifier",
        "invalid expression",
        "invalid statement",
        "invalid declaration",
        "invalid function",
        "invalid method",
        "invalid requires",
        "invalid ensures",
        "invalid invariant",
        "unexpected token",
        "unexpected character",
        "missing token",
        "missing character",
        "missing semicolon",
        "missing brace",
        "missing parenthesis",
        "missing bracket",
        "missing colon",
        "missing equals",
        "missing arrow",
        "missing dot",
        "missing comma",
        "missing space",
        "missing newline",
        "duplicate declaration",
        "duplicate definition",
        "duplicate identifier",
        "duplicate name",
        "duplicate symbol",
        "undefined identifier",
        "undefined name",
        "undefined symbol",
        "redeclaration",
        "redefinition",
        "already declared",
        "already defined",
        "already exists",
        "already present",
        "already used",
        "already assigned",
        "already initialized",
        "already called",
        "already accessed",
        "already indexed",
        "already member",
        "already operator",
        "already literal",
        "already identifier",
        "already token",
        "already character",
        "already number",
        "already string",
        "already comment",
        "already whitespace",
        "already newline"
    ]
    
    return any(indicator in output.lower() for indicator in compilation_error_indicators)

def extract_imports_from_code(content):
    """Extract import statements from Verus code."""
    import_lines = []
    lines = content.split('\n')
    
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('use '):
            import_lines.append(line)
        elif stripped and not stripped.startswith('//') and not stripped.startswith('/*'):
            # Stop at first non-import, non-comment line
            break
    
    return import_lines

def preserve_imports(original_code, new_code):
    """Preserve imports from original code in new code."""
    imports = extract_imports_from_code(original_code)
    if not imports:
        return new_code
    
    # Remove any existing imports from new code
    lines = new_code.split('\n')
    filtered_lines = []
    skip_imports = False
    
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('use '):
            skip_imports = True
            continue
        elif skip_imports and stripped and not stripped.startswith('//') and not stripped.startswith('/*'):
            # Found first non-import, non-comment line, stop skipping
            skip_imports = False
        
        if not skip_imports:
            filtered_lines.append(line)
    
    # Combine imports with filtered code
    return '\n'.join(imports + [''] + filtered_lines) 