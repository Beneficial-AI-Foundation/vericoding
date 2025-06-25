import os
import re
from pathlib import Path
from typing import List, Optional, Tuple

def contains_real_numbers(content: str) -> bool:
    """Check if the Dafny spec contains real numbers."""
    # Check for explicit real type declarations
    if re.search(r':\s*real\b', content):
        return True
    
    # Check for real literals (numbers with decimal points)
    if re.search(r'\b\d+\.\d+\b', content):
        return True
    
    return False

def translate_type(dafny_type: str) -> str:
    """Translate Dafny types to Verus types."""
    if not dafny_type or not isinstance(dafny_type, str):
        return ''
        
    dafny_type = dafny_type.strip()
    if not dafny_type:
        return ''
    
    # Basic type translations
    type_map = {
        'int': 'int',
        'bool': 'bool',
        'string': 'String',
        'char': 'char',
        'bv32': 'u32',  # Map bitvector types to unsigned integers
        'bv64': 'u64',
        'real': 'int',  # Map real to int since we skip files with real arithmetic
    }
    
    # Check basic types first
    if dafny_type in type_map:
        return type_map[dafny_type]
    
    # Handle arrays
    array_match = re.match(r'array<(.+)>', dafny_type)
    if array_match:
        inner_type = translate_type(array_match.group(1))
        return f'Vec<{inner_type}>'
    
    # Handle sequences
    seq_match = re.match(r'seq<(.+)>', dafny_type)
    if seq_match:
        inner_type = translate_type(seq_match.group(1))
        return f'Seq<{inner_type}>'
    
    # Handle maps
    map_match = re.match(r'map<([^,]+),\s*([^>]+)>', dafny_type)
    if map_match:
        key_type = translate_type(map_match.group(1))
        value_type = translate_type(map_match.group(2))
        return f'Map<{key_type}, {value_type}>'
    
    # Handle tuples
    if dafny_type.startswith('(') and dafny_type.endswith(')'):
        # Split by commas but handle nested types
        content = dafny_type[1:-1]  # Remove outer parentheses
        if not content.strip():
            return '()'
            
        # Simple split for now - we can make this more sophisticated if needed
        types = []
        current = ''
        nesting = 0
        
        for char in content:
            if char == '(':
                nesting += 1
            elif char == ')':
                nesting -= 1
            elif char == ',' and nesting == 0:
                if current.strip():
                    types.append(current.strip())
                current = ''
                continue
            current += char
            
        if current.strip():
            types.append(current.strip())
            
        if not types:
            return '()'
            
        translated_types = [translate_type(t) for t in types]
        return f'({", ".join(translated_types)})'
    
    # If we don't recognize the type, return it as is
    return dafny_type

def translate_expression(expr: str) -> str:
    """Translate Dafny expressions to Verus expressions."""
    if not expr or not isinstance(expr, str):
        return ''
        
    # Remove trailing semicolons
    expr = expr.strip()
    if expr.endswith(';'):
        expr = expr[:-1].strip()
    
    # Replace array/sequence length (.Length -> .len())
    expr = re.sub(r'\.Length\b', '.len()', expr)
    expr = re.sub(r'\|([^|]+)\|', r'\1.len()', expr)
    
    # Replace array indexing with spec_index
    expr = re.sub(r'(\w+)\[([^\]]+)\]', r'\1.spec_index(\2)', expr)
    
    # Replace logical operators
    expr = expr.replace('==>', '==>')
    expr = expr.replace('<=>', 'iff')
    expr = expr.replace('&&', '&&')
    expr = expr.replace('||', '||')
    expr = expr.replace(' and ', ' && ')
    expr = expr.replace(' or ', ' || ')
    
    # Replace quantifiers with proper type annotations and spacing
    def replace_quantifier(match):
        quant_type = match.group(1)  # forall or exists
        vars_str = match.group(2)
        # Split variables and add type annotations
        vars = [v.strip() for v in vars_str.split(',')]
        typed_vars = [f'{v}: int' if ':' not in v else v for v in vars]
        return f'{quant_type} |{", ".join(typed_vars)}|'
    
    # Handle quantifiers (forall and exists)
    expr = re.sub(r'(forall|exists)\s*\|([^|]+)\|', replace_quantifier, expr)
    
    return expr

def parse_method(content: str) -> Tuple[str, str, str, List[str], List[str]]:
    """Parse a Dafny method and return its components.
    Only matches methods with empty bodies (specification-only methods).
    Returns (name, params, returns, requires, ensures)."""
    # Extract method signature with empty body
    method_match = re.search(r'method\s+(\w+)\s*\((.*?)\)\s*returns\s*\((.*?)\)(?:\s*requires[^{]*)*(?:\s*ensures[^{]*)*\s*{\s*}', content, re.DOTALL)
    if not method_match:
        return '', '', '', [], []
    
    name = method_match.group(1)
    params = method_match.group(2)
    returns = method_match.group(3)
    
    # Extract requires clauses from the matched method
    requires = []
    for req in re.finditer(r'requires\s+([^{;]+?(?:;|\s*(?=requires|ensures|{)))', method_match.group(0)):
        requires.append(req.group(1).strip())
    
    # Extract ensures clauses from the matched method
    ensures = []
    for ens in re.finditer(r'ensures\s+([^{;]+?(?:;|\s*(?=requires|ensures|{)))', method_match.group(0)):
        ensures.append(ens.group(1).strip())
    
    return name, params, returns, requires, ensures

def translate_params(params: str, is_return_type: bool = False) -> str:
    """Translate Dafny parameters to Verus parameters.
    If is_return_type is True, wrap single parameters in parentheses."""
    if not params.strip():
        return ''
    
    param_list = []
    for param in params.split(','):
        param = param.strip()
        if not param:
            continue
            
        # Handle parameters with type annotations
        if ':' in param:
            name, type_str = param.split(':', 1)  # Split on first colon only
            translated_type = translate_type(type_str.strip())
            param_list.append(f'{name.strip()}: {translated_type}')
        else:
            # For parameters without type annotations, keep them as is
            param_list.append(param)
    
    result = ', '.join(param_list)
    
    # For return types, always wrap in parentheses
    if is_return_type:
        return f'({result})'
    
    return result

def get_default_value(type_str: str) -> str:
    """Generate a default value for a given Verus type."""
    # Remove outer parentheses if present (for return types)
    if type_str.startswith('(') and type_str.endswith(')'):
        type_str = type_str[1:-1]
    
    # If it's a named return value, extract the type
    if ':' in type_str:
        _, type_str = type_str.split(':', 1)
        type_str = type_str.strip()
    
    # Handle basic types
    if type_str == 'int':
        return '0'
    elif type_str == 'bool':
        return 'false'
    elif type_str == 'String':
        return 'String::new()'
    elif type_str == 'char':
        return "'\\0'"
    
    # Handle sequences
    seq_match = re.match(r'Seq<(.+)>', type_str)
    if seq_match:
        return 'Seq::empty()'
    
    # Handle vectors
    vec_match = re.match(r'Vec<(.+)>', type_str)
    if vec_match:
        return 'Vec::new()'
    
    # Handle maps
    map_match = re.match(r'Map<(.+)>', type_str)
    if map_match:
        return 'Map::empty()'
    
    # Handle tuples
    if ',' in type_str:
        types = [t.strip() for t in type_str.split(',')]
        default_values = [get_default_value(t) for t in types]
        return f'({", ".join(default_values)})'
    
    # Default to 0 for unknown types
    return '0'

def translate_spec(dafny_file: str) -> Optional[str]:
    """Translate a Dafny specification file to Verus."""
    with open(dafny_file, 'r') as f:
        content = f.read()
    
    # Skip files containing real numbers
    if contains_real_numbers(content):
        return None
    
    # Extract predicates first
    predicate_matches = re.finditer(r'predicate\s+(\w+)\s*\((.*?)\)\s*\{([^}]+)\}', content, re.DOTALL)
    predicates = []
    for match in predicate_matches:
        name = match.group(1)
        params = match.group(2)
        body = match.group(3).strip()
        
        translated_params = translate_params(params)
        translated_body = translate_expression(body)
        
        predicate = f'spec fn {name}({translated_params}) -> bool {{\n    {translated_body}\n}}'
        predicates.append(predicate)
    
    # Extract and translate method
    name, params, returns, requires, ensures = parse_method(content)
    if not name:
        if not predicates:
            return None
        verus_spec = [
            '#[allow(unused_imports)]',
            'use builtin::*;',
            '#[allow(unused_imports)]',
            'use builtin_macros::*;',
            '',
            'verus! {',
            '',
            'fn main() {',
            '}',
            ''
        ]
        verus_spec.extend(predicates)
        verus_spec.extend(['', '}'])
        return '\n'.join(verus_spec)
    
    translated_params = translate_params(params)
    translated_returns = translate_params(returns, is_return_type=True)
    
    # Build the Verus method
    verus_spec = []
    verus_spec.append('#[allow(unused_imports)]')
    verus_spec.append('use builtin::*;')
    verus_spec.append('#[allow(unused_imports)]')
    verus_spec.append('use builtin_macros::*;')
    verus_spec.append('')
    verus_spec.append('verus! {')
    verus_spec.append('')
    
    # Add main function
    verus_spec.append('fn main() {')
    verus_spec.append('}')
    verus_spec.append('')
    
    # Add predicates if any
    if predicates:
        verus_spec.extend(predicates)
        verus_spec.append('')  # Empty line between predicates and function
    
    # Add the function
    verus_spec.append(f'fn {name}({translated_params}) -> {translated_returns}')
    
    # Combine all requires into one clause
    if requires:
        requires_lines = [translate_expression(req.strip()) for req in requires]
        verus_spec.append('    requires')
        for i, req in enumerate(requires_lines):
            if i == len(requires_lines) - 1:
                verus_spec.append(f'        {req}')
            else:
                verus_spec.append(f'        {req},')
    
    # Combine all ensures into one clause
    if ensures:
        ensures_lines = [translate_expression(ens.strip()) for ens in ensures]
        verus_spec.append('    ensures')
        for i, ens in enumerate(ensures_lines):
            if i == len(ensures_lines) - 1:
                verus_spec.append(f'        {ens}')
            else:
                verus_spec.append(f'        {ens},')
    
    verus_spec.append('{')
    
    # Add default return value
    default_value = get_default_value(translated_returns)
    verus_spec.append(f'    return {default_value};')
    
    verus_spec.append('}')
    verus_spec.append('')  # Empty line for better readability
    verus_spec.append('}')  # Close verus! block
    
    return '\n'.join(verus_spec)

def process_directory(input_dir: str, output_dir: str):
    """Process all Dafny files in a directory and its subdirectories."""
    input_path = Path(input_dir)
    output_path = Path(output_dir)
    
    skipped_files = []
    processed_files = []
    error_files = []
    
    for dafny_file in input_path.rglob('*.dfy'):
        # Skip files in 'code_from_spec' directories
        if 'code_from_spec' in str(dafny_file):
            continue
            
        # Create corresponding output path
        rel_path = dafny_file.relative_to(input_path)
        output_file = output_path / rel_path.with_suffix('.rs')
        
        try:
            # Translate the spec
            verus_spec = translate_spec(str(dafny_file))
            
            if verus_spec is None:
                skipped_files.append(rel_path)
                continue
                
            # Create output directory if it doesn't exist
            output_file.parent.mkdir(parents=True, exist_ok=True)
            
            # Write the translated spec
            with open(output_file, 'w') as f:
                f.write('// Translated from Dafny\n')
                f.write('#[allow(unused_imports)]\nuse builtin::*;\n')
                f.write('#[allow(unused_imports)]\nuse builtin_macros::*;\n\n')
                f.write(verus_spec)
                
            processed_files.append(rel_path)
        except Exception as e:
            error_files.append((rel_path, str(e)))
    
    print(f"\nProcessed {len(processed_files)} files:")
    for f in processed_files:
        print(f"  - {f}")
        
    print(f"\nSkipped {len(skipped_files)} files containing real numbers:")
    for f in skipped_files:
        print(f"  - {f}")
        
    if error_files:
        print(f"\nErrors in {len(error_files)} files:")
        for f, error in error_files:
            print(f"  - {f}: {error}")

if __name__ == '__main__':
    input_dir = 'dafny/benchmarks/dafny-bench_specs'
    output_dir = 'src/verus_specs_no_llm/translations'
    process_directory(input_dir, output_dir) 