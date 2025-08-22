#!/usr/bin/env python3
"""
Vericode Parser Module
Handles parsing, extraction, and manipulation of Dafny code blocks.
"""

import os
import re
import subprocess

def find_dafny_files(directory):
    """Find all .dfy files in a directory."""
    try:
        files = os.listdir(directory)
        return [os.path.join(directory, f) for f in files if f.endswith(".dfy")]
    except Exception as e:
        print(f"Error reading directory {directory}: {e}")
        return []

def extract_dafny_code(output):
    """Extract Dafny code from LLM response."""
    # First try to extract from code blocks
    code_block_match = re.search(r'```dafny\n(.*?)```', output, re.DOTALL | re.IGNORECASE)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(code)
        return code
    
    # If no code block, try to find Dafny code patterns
    lines = output.split('\n')
    dafny_lines = []
    in_code = False
    
    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (line.strip().startswith('Looking at') or
            line.strip().startswith('The errors show that:') or
            line.strip().startswith('The issue is in') or
            line.strip().startswith('This function will be') or
            line.strip().startswith('Below is a Dafny program') or
            line.strip().startswith('Theo note:') or
            line.strip().startswith('// This function will be') or
            line.strip().startswith('// Below is a Dafny program') or
            line.strip().startswith('// Theo note:') or
            line.strip().startswith('```') or
            line.strip().startswith('1.') or
            line.strip().startswith('2.') or
            line.strip().startswith('3.') or
            line.strip().startswith('4.') or
            line.strip().startswith('5.')):
            continue
        
        # Start collecting when we see Dafny keywords, block markers, or comment structures
        if (line.find('method ') != -1 or 
            line.find('function ') != -1 or 
            line.find('lemma ') != -1 or 
            line.find('predicate ') != -1 or
            line.find('opaque ') != -1 or
            line.find('ghost ') != -1 or
            line.find('requires ') != -1 or
            line.find('ensures ') != -1 or
            line.find('invariant ') != -1 or
            line.find('decreases ') != -1 or
            # Block markers
            line.strip().startswith('//ATOM') or
            line.strip().startswith('//SPEC') or
            line.strip().startswith('//IMPL') or
            # Comment markers
            line.strip().startswith('/* code modified by LLM') or
            line.strip().startswith('// ATOMS') or
            line.strip().startswith('/*') or
            line.strip().startswith('*/')):
            in_code = True
        
        if in_code:
            dafny_lines.append(line)
    
    if dafny_lines:
        code = '\n'.join(dafny_lines).strip()
        code = fix_incomplete_code(code)
        return code
    
    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(code)
    return code

def fix_incomplete_code(code):
    """Fix common incomplete code patterns."""
    lines = code.split('\n')
    fixed_lines = []
    in_block = None  # Track current block type (ATOM, SPEC, or IMPL)
    
    for i, line in enumerate(lines):
        # Track block type
        if line.strip().startswith('//ATOM'):
            in_block = 'ATOM'
        elif line.strip().startswith('//SPEC'):
            in_block = 'SPEC'
        elif line.strip().startswith('//IMPL'):
            in_block = 'IMPL'
        
        # Fix incomplete string literals
        if ':= "' in line and '";' not in line:
            if line.strip().endswith(':= "') or line.strip().endswith(':= ""'):
                line = re.sub(r':= ""?$', ':= "";', line)
            elif line.strip().endswith('"'):
                line = line + ';'
        
        # Fix incomplete variable declarations
        if 'var ' in line and ' := ' in line and not line.endswith(';'):
            if line.strip().endswith(':= ""'):
                line = line + ';'
            elif line.strip().endswith(':= "') or line.strip().endswith(':='):
                line = re.sub(r':= ""?$', ':= "";', line)
        
        # Fix incomplete method bodies
        if line.strip().startswith('method ') and '{' not in line:
            # Look ahead to see if there's a method body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        # Fix incomplete function bodies
        if line.strip().startswith('function ') and '{' not in line:
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function ') or lines[j].strip().startswith('lemma '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        # Fix incomplete lemma bodies
        if line.strip().startswith('lemma ') and '{' not in line:
            # Look ahead to see if there's a lemma body
            has_body = False
            for j in range(i + 1, len(lines)):
                if lines[j].strip().startswith('{'):
                    has_body = True
                    break
                if lines[j].strip().startswith('method ') or lines[j].strip().startswith('function ') or lines[j].strip().startswith('lemma '):
                    break
            if not has_body and in_block != 'SPEC':  # Don't add body for SPEC blocks
                line = line + '\n{\n}'
        
        fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def extract_impl_blocks(code):
    """Extract IMPL blocks using a robust regex pattern that includes all lines after //IMPL, including the signature line, up to the next block marker."""
    pattern = r'//\s*IMPL[^\n]*\n([\s\S]*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_spec_blocks(code):
    """Extract SPEC blocks from original code."""
    # Handle both //SPEC and // SPEC, with optional spec names and constraints
    pattern = r'//\s*SPEC(?:\s+\[[^\]]+\])?(?:\s+[^\n]*)?\n(?://CONSTRAINTS:[^\n]*\n)?(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_atom_blocks(code):
    """Extract ATOM blocks from original code."""
    # Handle both //ATOM and // ATOM, and any comments after the marker
    pattern = r'//\s*ATOM(?:\s+[^\n]*)?\n(.*?)(?=//(?:ATOM|SPEC|IMPL)|$)'
    matches = re.findall(pattern, code, re.DOTALL)
    return matches

def extract_specification(code_block):
    """Extract the specification part (signature + requires + ensures) from a code block."""
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
    """Extract method/function/lemma signature from code block."""
    lines = code_block.split('\n')
    for line in lines:
        # Strip leading whitespace before checking for keywords
        stripped = line.strip()
        if any(keyword in stripped for keyword in ['method ', 'function ', 'lemma ']):
            # Return the line up to the first { or requires/ensures
            signature = stripped.split('{')[0].split('requires')[0].split('ensures')[0].strip()
            return signature
    return None

def merge_spec_with_body(original_spec, generated_body):
    """Merge original specification with generated body."""
    if not original_spec or not generated_body:
        return None
    
    # Combine spec and body
    return original_spec + '\n' + generated_body

def count_atoms_and_specs(code):
    """Count the number of ATOM and SPEC lines in the code."""
    lines = code.split('\n')
    nr_atoms = 0
    nr_spec = 0
    
    for line in lines:
        stripped_line = line.strip()
        # Handle both formats: //ATOM and // ATOM
        if stripped_line.startswith('//ATOM') or stripped_line.startswith('// ATOM'):
            nr_atoms += 1
        # Handle both formats: //SPEC and // SPEC  
        elif stripped_line.startswith('//SPEC') or stripped_line.startswith('// SPEC'):
            nr_spec += 1
    
    return nr_atoms, nr_spec

def detect_compilation_errors(output):
    """Detect if the output contains compilation errors."""
    compilation_error_indicators = [
        "resolution/type errors",
        "parse error", 
        "type error",
        "compilation error",
        "syntax error",
        "method call is not allowed to be used in an expression context",
        "expression is not allowed to invoke a method",
        "cannot resolve",
        "unresolved identifier",
        "invalid unaryexpression",
        "invalid expression",
        "invalid statement",
        "invalid declaration",
        "invalid function",
        "invalid method",
        "invalid lemma",
        "invalid predicate",
        "invalid requires",
        "invalid ensures",
        "invalid invariant",
        "invalid decreases",
        "invalid reads",
        "invalid modifies",
        "invalid frame",
        "invalid ghost",
        "invalid opaque",
        "invalid export",
        "invalid import",
        "invalid include",
        "invalid module",
        "invalid class",
        "invalid trait",
        "invalid datatype",
        "invalid codatatype",
        "invalid newtype",
        "invalid type",
        "invalid variable",
        "invalid constant",
        "invalid field",
        "invalid parameter",
        "invalid return",
        "invalid assignment",
        "invalid call",
        "invalid access",
        "invalid index",
        "invalid member",
        "invalid operator",
        "invalid literal",
        "invalid identifier",
        "invalid token",
        "invalid character",
        "invalid number",
        "invalid string",
        "invalid comment",
        "invalid whitespace",
        "invalid newline",
        "invalid end of file",
        "unexpected token",
        "unexpected character",
        "unexpected end of file",
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
        "missing end of file",
        "duplicate declaration",
        "duplicate definition",
        "duplicate identifier",
        "duplicate name",
        "duplicate symbol",
        "duplicate token",
        "duplicate character",
        "duplicate whitespace",
        "duplicate newline",
        "duplicate end of file",
        "undefined identifier",
        "undefined name",
        "undefined symbol",
        "undefined token",
        "undefined character",
        "undefined whitespace",
        "undefined newline",
        "undefined end of file",
        "redeclaration",
        "redefinition",
        "redeclaration of",
        "redefinition of",
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
        "already newline",
        "already end of file"
    ]
    
    return any(indicator in output.lower() for indicator in compilation_error_indicators) 