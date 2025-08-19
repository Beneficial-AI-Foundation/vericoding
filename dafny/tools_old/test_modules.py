#!/usr/bin/env python3
"""
Test script for the modularized vericode components.
"""

import os
import tempfile
from vericode_parser import (
    find_dafny_files, extract_dafny_code, extract_impl_blocks,
    extract_spec_blocks, extract_atom_blocks, count_atoms_and_specs
)
from vericode_checker import (
    verify_dafny_file, verify_atom_blocks, verify_specifications
)
from vericode_printer import (
    print_summary, save_results, print_file_result, print_help
)

def test_parser_functions():
    """Test parser functions."""
    print("Testing parser functions...")
    
    # Test file finding
    files = find_dafny_files(".")
    print(f"Found {len(files)} .dfy files in current directory")
    
    # Test code extraction
    test_code = """
    method test(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        y := x + 1;
    }
    """
    
    extracted = extract_dafny_code(test_code)
    print(f"Code extraction test: {'✅' if extracted else '❌'}")
    
    # Test block extraction
    test_blocks = """
    //ATOM
    method atom_method() {}
    
    //SPEC
    method spec_method(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        // Implementation here
    }
    
    //IMPL
    method impl_method(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        y := x + 1;
    }
    """
    
    atoms = extract_atom_blocks(test_blocks)
    specs = extract_spec_blocks(test_blocks)
    impls = extract_impl_blocks(test_blocks)
    
    print(f"ATOM blocks: {len(atoms)}")
    print(f"SPEC blocks: {len(specs)}")
    print(f"IMPL blocks: {len(impls)}")
    
    # Test counting
    nr_atoms, nr_spec = count_atoms_and_specs(test_blocks)
    print(f"Counted: {nr_atoms} ATOMs, {nr_spec} SPECs")

def test_checker_functions():
    """Test checker functions."""
    print("\nTesting checker functions...")
    
    # Create a simple valid Dafny file
    valid_dafny = """
    method test(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        y := x + 1;
    }
    """
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.dfy', delete=False) as f:
        f.write(valid_dafny)
        temp_file = f.name
    
    try:
        # Test verification
        result = verify_dafny_file(temp_file)
        print(f"Verification test: {'✅' if result['success'] else '❌'}")
        if not result['success']:
            print(f"  Error: {result['error']}")
    finally:
        os.unlink(temp_file)
    
    # Test block verification
    original = """
    //ATOM
    method atom() {}
    
    //SPEC
    method spec(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        // Implementation
    }
    """
    
    generated = """
    //ATOM
    method atom() {}
    
    //IMPL
    method spec(x: int) returns (y: int)
        requires x > 0
        ensures y > x
    {
        y := x + 1;
    }
    """
    
    atoms_ok = verify_atom_blocks(original, generated)
    specs_ok = verify_specifications(original, generated)
    
    print(f"ATOM verification: {'✅' if atoms_ok else '❌'}")
    print(f"SPEC verification: {'✅' if specs_ok else '❌'}")

def test_printer_functions():
    """Test printer functions."""
    print("\nTesting printer functions...")
    
    # Test results
    test_results = [
        {
            'file': 'test1.dfy',
            'success': True,
            'error': None,
            'nr_atoms': 2,
            'nr_spec': 1
        },
        {
            'file': 'test2.dfy',
            'success': False,
            'error': 'Verification failed',
            'nr_atoms': 1,
            'nr_spec': 0
        }
    ]
    
    # Test file result printing
    print("File results:")
    for result in test_results:
        print_file_result(result, verbose=True)
    
    # Test summary
    print("\nSummary:")
    print_summary(test_results, "./test_output")
    
    # Test help
    print("\nHelp:")
    print_help()

def main():
    """Run all tests."""
    print("=" * 60)
    print("TESTING MODULARIZED VERICODE COMPONENTS")
    print("=" * 60)
    
    test_parser_functions()
    test_checker_functions()
    test_printer_functions()
    
    print("\n" + "=" * 60)
    print("ALL TESTS COMPLETED")
    print("=" * 60)

if __name__ == "__main__":
    main() 