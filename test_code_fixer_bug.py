#!/usr/bin/env python3

"""Test case demonstrating the code_fixer bug that adds 'sorry' incorrectly."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from vericoding.processing.code_fixer import fix_incomplete_lean_code

def test_code_fixer_bug():
    """Demonstrate that fix_incomplete_lean_code incorrectly adds 'sorry'."""
    
    # This is valid Lean code with a complete function definition
    input_code = '''def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  (a < 0 && b > 0) || (a > 0 && b < 0)'''
    
    print("INPUT CODE:")
    print(input_code)
    print("\n" + "="*50 + "\n")
    
    # Run the code fixer
    fixed_code = fix_incomplete_lean_code(input_code)
    
    print("OUTPUT FROM fix_incomplete_lean_code:")
    print(fixed_code)
    print("\n" + "="*50 + "\n")
    
    # Check if 'sorry' was incorrectly added
    if 'sorry' in fixed_code and 'sorry' not in input_code:
        print("❌ BUG CONFIRMED: fix_incomplete_lean_code incorrectly added 'sorry'")
        print("This creates invalid Lean syntax!")
    else:
        print("✅ No bug detected - code was preserved correctly")

if __name__ == "__main__":
    test_code_fixer_bug()