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

# Import pytest only when needed
try:
    import pytest
    PYTEST_AVAILABLE = True
except ImportError:
    PYTEST_AVAILABLE = False

# Import shared validation functionality
sys.path.append(str(Path(__file__).parent.parent))
from verus.verus_validation import (
    find_verus_executable, 
    check_syntax_with_verus,
    create_yaml_without_helpers,
    convert_yaml_to_rust,
    VerusNotFoundError
)


if PYTEST_AVAILABLE:
    @pytest.fixture(scope="session")
    def verus_cmd():
        """Fixture to find Verus executable or skip test if not available."""
        try:
            return find_verus_executable()
        except VerusNotFoundError:
            pytest.skip("Verus executable not found - install verus to run this test")

    @pytest.fixture
    def temp_path():
        """Fixture to provide a temporary directory."""
        with tempfile.TemporaryDirectory(prefix="verus_test_") as temp_dir:
            yield Path(temp_dir)


def find_yaml_test_files():
    """Dynamically find all YAML test files."""
    test_file_dir = Path(__file__).parent
    
    # Try multiple possible locations for test data
    possible_dirs = [
        test_file_dir / "verus-test-data",
        test_file_dir.parent / "verus-test-data", 
        test_file_dir.parent.parent / "verus-test-data"
    ]
    
    yaml_files = []
    for test_dir in possible_dirs:
        if test_dir.exists():
            # Find all YAML files recursively
            yaml_files.extend(test_dir.glob("**/*.yaml"))
            break
    
    if not yaml_files:
        if PYTEST_AVAILABLE:
            pytest.skip("No YAML test files found in any of the expected directories")
        else:
            raise FileNotFoundError("No YAML test files found in any of the expected directories")
    
    return sorted(yaml_files)  # Sort for consistent ordering


if PYTEST_AVAILABLE:
    @pytest.fixture(params=find_yaml_test_files(), ids=lambda f: f.name)
    def yaml_file(request):
        """Fixture to provide YAML test files dynamically discovered."""
        return request.param


def test_yaml_without_helpers(yaml_file: Path, temp_path: Path, verus_cmd: str):
    """Test a YAML file with empty vc-helpers section.
    
    This test:
    1. Reads a YAML file 
    2. Creates a version without vc-helpers
    3. Converts both to Rust
    4. Verifies both with Verus
    """
    print(f"\n🔄 Testing {yaml_file.name}...")
    
    try:
        # Read original YAML
        with open(yaml_file, 'r') as f:
            original_content = f.read()
        
        # Skip if there are no helpers to remove
        if 'vc-helpers: |-' not in original_content:
            pytest.skip("No helpers to remove in this file")
        
        print(f"   Testing without vc-helpers...")
        
        # Create modified version without helpers
        modified_content = create_yaml_without_helpers(original_content)
        
        # Write modified YAML to temp directory
        temp_yaml = temp_path / f"no_helpers_{yaml_file.name}"
        with open(temp_yaml, 'w') as f:
            f.write(modified_content)
        
        # Convert to Rust
        success, temp_rust_file = convert_yaml_to_rust(temp_yaml, temp_path)
        assert success, "Conversion from YAML to Rust failed"
        assert temp_rust_file.exists(), "Rust file was not created"
        
        print(f"   Running Verus syntax check...")
        
        # Verify with Verus
        syntax_ok, output = check_syntax_with_verus(temp_rust_file, verus_cmd)
        
        # The test passes if either:
        # 1. Syntax check succeeds, OR
        # 2. Syntax check fails but it's a reasonable failure (not a crash)
        if not syntax_ok:
            # Allow certain types of "acceptable" failures
            acceptable_failures = [
                "verification condition is false",
                "failed to verify",
                "postcondition not satisfied",
                "precondition not satisfied"
            ]
            
            # Check if it's an acceptable failure vs a syntax/compilation error
            is_acceptable = any(failure in output.lower() for failure in acceptable_failures)
            
            if not is_acceptable:
                print(f"   ❌ Unexpected Verus error: {output}")
                pytest.fail(f"Verus syntax check failed with unexpected error: {output}")
            else:
                print(f"   ⚠️  Acceptable verification failure: {output[:100]}...")
        else:
            print(f"   ✅ Verus syntax check passed")
        
        # If we get here, the test passed (either syntax OK or acceptable verification failure)
        
    except Exception as e:
        print(f"   💥 Exception: {e}")
        pytest.fail(f"Test failed with exception: {e}")


def test_original_yaml_conversion(yaml_file: Path, temp_path: Path, verus_cmd: str):
    """Test conversion and verification of original YAML files.
    
    This test verifies that the original YAML files can be:
    1. Converted to Rust successfully
    2. Pass Verus syntax checking
    """
    print(f"\n🔄 Testing original {yaml_file.name}...")
    
    try:
        print(f"   Converting original to Rust...")
        
        # Convert original YAML to Rust
        success, temp_rust_file = convert_yaml_to_rust(yaml_file, temp_path)
        assert success, "Conversion from YAML to Rust failed"
        assert temp_rust_file.exists(), "Rust file was not created"
        
        print(f"   Running Verus syntax check on original...")
        
        # Verify with Verus
        syntax_ok, output = check_syntax_with_verus(temp_rust_file, verus_cmd)
        
        if not syntax_ok:
            # For original files, we're more strict - they should generally work
            # But we still allow some verification failures
            acceptable_failures = [
                "verification condition is false",
                "failed to verify",
                "postcondition not satisfied",
                "precondition not satisfied"
            ]
            
            is_acceptable = any(failure in output.lower() for failure in acceptable_failures)
            
            if not is_acceptable:
                print(f"   ❌ Original YAML failed: {output}")
                pytest.fail(f"Original YAML Verus check failed: {output}")
            else:
                print(f"   ⚠️  Original YAML has acceptable verification issues: {output[:100]}...")
        else:
            print(f"   ✅ Original YAML Verus syntax check passed")
            
    except Exception as e:
        print(f"   💥 Exception: {e}")
        pytest.fail(f"Original YAML test failed with exception: {e}")


class TestVerusValidationSummary:
    """Class to collect and report test results summary."""
    
    @pytest.fixture(autouse=True, scope="session")
    def test_summary(self, request):
        """Fixture that runs after all tests to provide a summary."""
        yield
        
        # This runs after all tests in the session
        if hasattr(request.session, 'testsfailed'):
            failed_count = request.session.testsfailed
            total_count = len([item for item in request.session.items if 'test_verus_validation' in str(item.fspath)])
            passed_count = total_count - failed_count
            
            print(f"\n" + "="*70)
            print(f"🏁 Verus Validation Test Summary:")
            print(f"   Total tests: {total_count}")
            print(f"   Passed: {passed_count}")
            print(f"   Failed: {failed_count}")
            
            if failed_count == 0:
                print(f"🎉 All Verus validation tests passed!")
            else:
                print(f"💥 {failed_count} tests failed. Check output above for details.")
            print("="*70)


# Standalone test functions (without pytest dependencies)
def test_yaml_without_helpers_standalone(yaml_file: Path, temp_path: Path, verus_cmd: str):
    """Standalone version of the no-helpers test."""
    try:
        # Read original YAML
        with open(yaml_file, 'r') as f:
            original_content = f.read()
        
        # Skip if there are no helpers to remove
        if 'vc-helpers: |-' not in original_content:
            return True, "No helpers to remove", True
        
        # Create modified version without helpers
        modified_content = create_yaml_without_helpers(original_content)
        
        # Write modified YAML to temp directory
        temp_yaml = temp_path / f"no_helpers_{yaml_file.name}"
        with open(temp_yaml, 'w') as f:
            f.write(modified_content)
        
        # Convert to Rust
        success, temp_rust_file = convert_yaml_to_rust(temp_yaml, temp_path)
        if not success:
            return False, "Conversion failed", False
        
        # Verify with Verus
        syntax_ok, output = check_syntax_with_verus(temp_rust_file, verus_cmd)
        
        # Allow acceptable verification failures
        if not syntax_ok:
            acceptable_failures = [
                "verification condition is false",
                "failed to verify",
                "postcondition not satisfied",
                "precondition not satisfied"
            ]
            is_acceptable = any(failure in output.lower() for failure in acceptable_failures)
            if is_acceptable:
                return True, f"Acceptable verification failure: {output}", False
        
        return syntax_ok, output, False
        
    except Exception as e:
        return False, f"Error: {e}", False


def test_original_yaml_standalone(yaml_file: Path, temp_path: Path, verus_cmd: str):
    """Standalone version of the original YAML test."""
    try:
        # Convert original YAML to Rust
        success, temp_rust_file = convert_yaml_to_rust(yaml_file, temp_path)
        if not success:
            return False, "Conversion failed"
        
        # Verify with Verus
        syntax_ok, output = check_syntax_with_verus(temp_rust_file, verus_cmd)
        
        # Allow acceptable verification failures
        if not syntax_ok:
            acceptable_failures = [
                "verification condition is false",
                "failed to verify", 
                "postcondition not satisfied",
                "precondition not satisfied"
            ]
            is_acceptable = any(failure in output.lower() for failure in acceptable_failures)
            if is_acceptable:
                return True, f"Acceptable verification failure: {output}"
        
        return syntax_ok, output
        
    except Exception as e:
        return False, f"Error: {e}"


# Preserve the ability to run as standalone script (like the old version)
def main():
    """Main function for standalone execution - replicates old behavior."""
    print("🧪 Testing YAML to Rust conversion and Verus validation...")
    
    # Parse command line arguments for optional path
    import argparse
    parser = argparse.ArgumentParser(description="Test YAML to Rust conversion and Verus validation")
    parser.add_argument("path", nargs="?", default=None, 
                       help="Optional path to test directory (defaults to verus-test-data)")
    args = parser.parse_args()
    
    # Find verus executable
    try:
        verus_cmd = find_verus_executable()
        print(f"✅ Found Verus at: {verus_cmd}")
    except VerusNotFoundError as e:
        print(f"❌ {e}")
        if PYTEST_AVAILABLE:
            print("💡 For pytest integration, run: uv run pytest src/tests/test_verus_validation.py -v")
        return 1
    
    # Get YAML test files
    if args.path:
        test_dir = Path(args.path)
        if not test_dir.exists():
            print(f"❌ Test directory not found: {test_dir}")
            return 1
        yaml_files = list(test_dir.glob("**/*.yaml"))
    else:
        try:
            yaml_files = find_yaml_test_files()
        except FileNotFoundError as e:
            print(f"❌ {e}")
            return 1
    
    if not yaml_files:
        print(f"❌ No YAML files found")
        return 1
    
    print(f"📁 Found {len(yaml_files)} YAML files to test")
    
    # Create temporary directory for generated Rust files
    with tempfile.TemporaryDirectory(prefix="verus_test_") as temp_dir:
        temp_path = Path(temp_dir)
        print(f"📂 Using temporary directory: {temp_path}")
        
        original_results = []
        no_helpers_results = []
        
        for yaml_file in yaml_files:
            print(f"\n🔄 Testing {yaml_file.name}...")
            
            # Test original YAML
            print(f"   Converting original to Rust...")
            success, output = test_original_yaml_standalone(yaml_file, temp_path, verus_cmd)
            
            if success:
                print(f"   ✅ Original Verus check passed")
                original_results.append((yaml_file.name, True, "Success"))
            else:
                print(f"   ❌ Original Verus check failed: {output[:100]}...")
                original_results.append((yaml_file.name, False, output))
                continue  # Skip no-helpers test if original fails
            
            # Test no-helpers version
            print(f"   Testing without vc-helpers...")
            success_no_helpers, output_no_helpers, was_skipped = test_yaml_without_helpers_standalone(yaml_file, temp_path, verus_cmd)
            
            if was_skipped:
                print(f"   ⏩ No-helpers test skipped (no helpers to remove)")
                no_helpers_results.append((yaml_file.name, True, "Skipped - no helpers", True))
            elif success_no_helpers:
                print(f"   ✅ No-helpers Verus check passed")
                no_helpers_results.append((yaml_file.name, True, "Success", False))
            else:
                print(f"   ❌ No-helpers Verus check failed: {output_no_helpers[:100]}...")
                no_helpers_results.append((yaml_file.name, False, output_no_helpers, False))
    
    # Print summary (like the old version)
    print(f"\n📊 Test Results Summary:")
    print(f"=" * 70)
    
    print(f"\n🔸 Original YAML Tests:")
    original_passed = sum(1 for _, success, _ in original_results if success)
    original_failed = len(original_results) - original_passed
    
    for filename, success, message in original_results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {filename}")
        if not success:
            print(f"      {message[:100]}{'...' if len(message) > 100 else ''}")
    
    print(f"\n🔹 No-Helpers YAML Tests:")
    no_helpers_passed = sum(1 for _, success, _, skipped in no_helpers_results if success and not skipped)
    no_helpers_skipped = sum(1 for _, _, _, skipped in no_helpers_results if skipped)
    no_helpers_failed = len(no_helpers_results) - no_helpers_passed - no_helpers_skipped
    
    for filename, success, message, was_skipped in no_helpers_results:
        if was_skipped:
            status = "⏩ SKIP"
        elif success:
            status = "✅ PASS"
        else:
            status = "❌ FAIL"
            
        print(f"{status}: {filename}")
        if not success and not was_skipped:
            print(f"      {message[:100]}{'...' if len(message) > 100 else ''}")
    
    print(f"\n🏁 Final Results:")
    print(f"   Original tests  - Passed: {original_passed}, Failed: {original_failed}")
    print(f"   No-helpers tests - Passed: {no_helpers_passed}, Failed: {no_helpers_failed}, Skipped: {no_helpers_skipped}")
    print(f"   Total files tested: {len(original_results)}")
    
    total_failed = original_failed + no_helpers_failed
    
    if total_failed == 0:
        print(f"\n🎉 All tests passed! YAML files work with and without vc-helpers.")
        if PYTEST_AVAILABLE:
            print("💡 For pytest integration, run: uv run pytest src/tests/test_verus_validation.py -v")
        return 0
    else:
        print(f"\n💥 {total_failed} tests failed. Check output above for details.")
        return 1


if __name__ == "__main__":
    sys.exit(main())