#!/usr/bin/env python3
import re
import os

def test_regex_on_file(file_path):
    """Test regex patterns on a specific file."""
    print(f"Testing file: {file_path}")
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    print("File content:")
    print(content)
    print("\n" + "="*50)
    
    # Test the function pattern
    function_pattern = r'fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*\}'
    function_matches = re.findall(function_pattern, content, re.DOTALL)
    
    print(f"Function matches: {function_matches}")
    
    for match in function_matches:
        print(f"\nChecking function: {match}")
        # Find the full function definition
        full_pattern = r'fn\s+' + re.escape(match) + r'\s*\([^)]*\)\s*->\s*\([^)]*\)\s*(?:ensures[^{]*)?\s*\{[^{}]*\}'
        full_match = re.search(full_pattern, content, re.DOTALL)
        if full_match:
            function_text = full_match.group(0)
            print(f"Full function text: {function_text}")
            
            # Check conditions
            is_spec = 'spec fn' in function_text
            has_return_false = 'return false;' in function_text
            has_return_true = 'return true;' in function_text
            has_return_0 = 'return 0;' in function_text
            has_return_1 = 'return 1;' in function_text
            has_todo = 'TODO' in function_text.upper()
            
            print(f"  Is spec: {is_spec}")
            print(f"  Has return false: {has_return_false}")
            print(f"  Has return true: {has_return_true}")
            print(f"  Has return 0: {has_return_0}")
            print(f"  Has return 1: {has_return_1}")
            print(f"  Has TODO: {has_todo}")
            
            if (not is_spec and 
                (has_return_false or has_return_true or has_return_0 or has_return_1 or has_todo)):
                print(f"  ✅ This function should be targeted!")
            else:
                print(f"  ❌ This function should NOT be targeted")

if __name__ == "__main__":
    # Test on a few files
    test_files = [
        "src/verus_specs_no_llm/translations/specs_benches/VerusProofSynthesisBench/MBPP/task_id_454.rs",
        "src/verus_specs_no_llm/translations/specs_benches/VerusProofSynthesisBench/MBPP/task_id_804.rs"
    ]
    
    for file_path in test_files:
        if os.path.exists(file_path):
            test_regex_on_file(file_path)
            print("\n" + "="*80 + "\n")
        else:
            print(f"File not found: {file_path}") 