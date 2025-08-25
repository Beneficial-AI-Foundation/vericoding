#!/usr/bin/env python3
"""
Test script that converts YAML files back to Rust and verifies them with Verus.

For each YAML file in the tests directory:
1. Convert YAML back to Rust using convert_from_yaml.py
2. Run verus on the generated Rust file
3. Verify verus exits with code 0
4. Clean up generated files
"""

import tempfile
import sys
from pathlib import Path

# Import shared validation functionality
sys.path.append(str(Path(__file__).parent.parent))
from verus_validation import (
    find_verus_executable, 
    verify_rust_with_verus, 
    create_yaml_without_helpers,
    convert_yaml_to_rust,
    VerusNotFoundError
)

def test_yaml_without_helpers(yaml_file: Path, temp_path: Path, verus_cmd: str) -> tuple[bool, str]:
    """Test a YAML file with empty vc-helpers section."""
    try:
        # Read original YAML
        with open(yaml_file, 'r') as f:
            original_content = f.read()
        
        # Skip if there are no helpers to remove
        if 'vc-helpers: |-' not in original_content:
            return True, "No helpers to remove - skipped"
        
        # Create modified version without helpers
        modified_content = create_yaml_without_helpers(original_content)
        
        # Write modified YAML to temp directory
        temp_yaml = temp_path / f"no_helpers_{yaml_file.name}"
        with open(temp_yaml, 'w') as f:
            f.write(modified_content)
        
        # Convert to Rust
        success, temp_rust_file = convert_yaml_to_rust(temp_yaml, temp_path)
        if not success:
            return False, "Conversion failed"
        
        # Verify with Verus
        success, output = verify_rust_with_verus(temp_rust_file, verus_cmd)
        return success, output
        
    except Exception as e:
        return False, f"Error: {e}"

def main():
    """Main test function."""
    print("🧪 Testing YAML to Rust conversion and Verus validation...")
    
    # Find verus executable - will raise VerusNotFoundError if not found
    try:
        verus_cmd = find_verus_executable()
        print(f"✅ Found Verus at: {verus_cmd}")
    except VerusNotFoundError as e:
        print(f"❌ {e}")
        return 1
    
    # Get project root and tests directory
    project_root = Path(__file__).parent.parent.parent
    tests_dir = Path(__file__).parent / "verus-test-data"
    
    if not tests_dir.exists():
        print(f"❌ Tests directory not found: {tests_dir}")
        return 1
    
    # Find all YAML files in tests directory
    yaml_files = list(tests_dir.glob("*.yaml"))
    if not yaml_files:
        print(f"❌ No YAML files found in {tests_dir}")
        return 1
    
    print(f"📁 Found {len(yaml_files)} YAML files to test")
    
    # Create temporary directory for generated Rust files
    with tempfile.TemporaryDirectory(prefix="verus_test_") as temp_dir:
        temp_path = Path(temp_dir)
        print(f"📂 Using temporary directory: {temp_path}")
        
        results = []
        no_helpers_results = []
        
        for yaml_file in yaml_files:
            print(f"\n🔄 Testing {yaml_file.name}...")
            
            # Step 1: Test original YAML
            print(f"   Converting original to Rust...")
            success, temp_rust_file = convert_yaml_to_rust(yaml_file, temp_path)
            if not success:
                results.append((yaml_file.name, False, "Conversion failed"))
                continue
            
            print(f"   Running Verus syntax check on original...")
            success, output = verify_rust_with_verus(temp_rust_file, verus_cmd)
            
            if success:
                print(f"   ✅ Original Verus syntax check passed")
                results.append((yaml_file.name, True, "Success"))
            else:
                print(f"   ❌ Original Verus syntax check failed")
                print(f"   Output: {output}")
                results.append((yaml_file.name, False, f"Verus failed: {output}"))
                continue  # Skip no-helpers test if original fails
            
            # Step 2: Test version without vc-helpers
            print(f"   Testing without vc-helpers...")
            success_no_helpers, output_no_helpers = test_yaml_without_helpers(yaml_file, temp_path, verus_cmd)
            
            if success_no_helpers:
                if "skipped" in output_no_helpers:
                    print(f"   ⏩ No-helpers test skipped (no helpers to remove)")
                    no_helpers_results.append((yaml_file.name, True, "Skipped - no helpers"))
                else:
                    print(f"   ✅ No-helpers Verus syntax check passed")
                    no_helpers_results.append((yaml_file.name, True, "Success"))
            else:
                print(f"   ❌ No-helpers Verus syntax check failed")
                print(f"   Output: {output_no_helpers}")
                no_helpers_results.append((yaml_file.name, False, f"No-helpers failed: {output_no_helpers}"))
    
    # Print summary
    print(f"\n📊 Test Results Summary:")
    print(f"=" * 70)
    
    print(f"\n🔸 Original YAML Tests:")
    original_passed = 0
    original_failed = 0
    
    for filename, success, message in results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {filename}")
        if not success:
            print(f"      {message[:100]}{'...' if len(message) > 100 else ''}")
        
        if success:
            original_passed += 1
        else:
            original_failed += 1
    
    print(f"\n🔹 No-Helpers YAML Tests:")
    no_helpers_passed = 0
    no_helpers_failed = 0
    no_helpers_skipped = 0
    
    for filename, success, message in no_helpers_results:
        if "skipped" in message.lower():
            status = "⏩ SKIP"
            no_helpers_skipped += 1
        elif success:
            status = "✅ PASS"
            no_helpers_passed += 1
        else:
            status = "❌ FAIL"
            no_helpers_failed += 1
            
        print(f"{status}: {filename}")
        if not success and "skipped" not in message.lower():
            print(f"      {message[:100]}{'...' if len(message) > 100 else ''}")
    
    print(f"\n🏁 Final Results:")
    print(f"   Original tests  - Passed: {original_passed}, Failed: {original_failed}")
    print(f"   No-helpers tests - Passed: {no_helpers_passed}, Failed: {no_helpers_failed}, Skipped: {no_helpers_skipped}")
    print(f"   Total files tested: {len(results)}")
    
    total_failed = original_failed + no_helpers_failed
    
    if total_failed == 0:
        print(f"\n🎉 All tests passed! YAML files work with and without vc-helpers.")
        return 0
    else:
        print(f"\n💥 {total_failed} tests failed. Check output above for details.")
        return 1

if __name__ == "__main__":
    sys.exit(main())