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
    # Replace array/sequence length (.Length -> .len())
    expr = re.sub(r'\.Length\b', '.len()', expr)
    expr = re.sub(r'\|([^|]+)\|', r'\1.len()', expr)
    
    # Replace array indexing
    expr = re.sub(r'(\w+)\[([^\]]+)\]', r'\1[\2]', expr)
    
    # Replace logical operators
    expr = expr.replace('==>', '==>')
    expr = expr.replace('<=>', 'iff')
    expr = expr.replace('&&', 'and')
    expr = expr.replace('||', 'or')
    
    # Replace quantifiers with proper type annotations
    def replace_quantifier(match):
        quant_type = match.group(1)  # forall or exists
        vars_str = match.group(2)
        # Split variables and add type annotations
        vars = [v.strip() for v in vars_str.split(',')]
        typed_vars = [f'{v}: int' if ':' not in v else v for v in vars]
        return f'{quant_type}|{", ".join(typed_vars)}|'
    
    # Handle quantifiers (forall and exists)
    expr = re.sub(r'(forall|exists)\s+([^:]+)::', replace_quantifier, expr)
    
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
    requires = re.findall(r'requires\s+([^{]+?)(?=\s*(?:requires|ensures|{))', method_match.group(0))
    
    # Extract ensures clauses from the matched method
    ensures = re.findall(r'ensures\s+([^{]+?)(?=\s*(?:requires|ensures|{))', method_match.group(0))
    
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
    
    # For return types, if there's only one parameter, wrap it in parentheses
    if is_return_type and len(param_list) == 1 and ':' in param_list[0]:
        return f'({result})'
    
    return result

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
        return 'verus! {\n\n' + '\n\n'.join(predicates) + '\n\n}'
    
    translated_params = translate_params(params)
    translated_returns = translate_params(returns, is_return_type=True)
    
    # Build the Verus method
    verus_spec = []
    verus_spec.append('verus! {')
    verus_spec.append('')  # Empty line for better readability
    
    # Add predicates if any
    if predicates:
        verus_spec.extend(predicates)
        verus_spec.append('')  # Empty line between predicates and function
    
    # Add the function
    verus_spec.append(f'fn {name}({translated_params}) -> {translated_returns}')
    
    # Combine all requires into one clause
    if requires:
        requires_lines = [translate_expression(req.strip()) for req in requires]
        verus_spec.append('    requires ' + ',\n             '.join(requires_lines))
    
    # Combine all ensures into one clause
    if ensures:
        ensures_lines = [translate_expression(ens.strip()) for ens in ensures]
        verus_spec.append('    ensures ' + ',\n            '.join(ensures_lines))
    
    verus_spec.append('{')
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