#!/usr/bin/env python3
"""
Test script that converts YAML files back to Rust and verifies them with Verus.

For each YAML file in the tests directory:
1. Convert YAML back to Rust using convert_from_yaml.py
2. Run verus on the generated Rust file
3. Verify verus exits with code 0
4. Clean up generated files
"""

import subprocess
import tempfile
import sys
from pathlib import Path
import shutil
import os

def find_verus_executable():
    """Find the verus executable in PATH or common locations."""
    # Check if verus is in PATH
    if shutil.which("verus"):
        return "verus"
    
    # Check common installation locations
    common_paths = [
        "/usr/local/bin/verus",
        "/usr/bin/verus", 
        Path.home() / ".cargo/bin/verus",
        Path.home() / "bin/verus"
    ]
    
    for path in common_paths:
        if Path(path).exists():
            return str(path)
    
    return None

def convert_yaml_to_rust(yaml_path: Path, temp_dir: Path) -> tuple[bool, Path]:
    """Convert YAML file to Rust using convert_from_yaml.py, output to temp directory."""
    try:
        # Create a copy of the YAML file in temp directory to avoid modifying tests dir
        temp_yaml = temp_dir / yaml_path.name
        if temp_yaml != yaml_path:  # Only copy if different paths
            shutil.copy2(yaml_path, temp_yaml)
        else:
            temp_yaml = yaml_path
        
        result = subprocess.run([
            "uv", "run", "src/convert_from_yaml.py",
            str(temp_yaml),
            "--suffix", "rs"
        ], capture_output=True, text=True, cwd=Path(__file__).parent.parent.parent)
        
        if result.returncode != 0:
            print(f"❌ Failed to convert {yaml_path.name}:")
            print(f"   stdout: {result.stdout}")
            print(f"   stderr: {result.stderr}")
            return False, Path()
            
        # The convert script creates the .rs file next to the yaml file
        temp_rust = temp_yaml.with_suffix('.rs')
        return temp_rust.exists(), temp_rust
        
    except Exception as e:
        print(f"❌ Error converting {yaml_path.name}: {e}")
        return False, Path()

def verify_rust_with_verus(rust_path: Path, verus_cmd: str) -> tuple[bool, str]:
    """Run verus --no-verify on the Rust file and return success status and output."""
    try:
        result = subprocess.run([
            verus_cmd, "--no-verify", str(rust_path)
        ], capture_output=True, text=True, timeout=30)
        
        success = result.returncode == 0
        output = f"stdout: {result.stdout}\nstderr: {result.stderr}" if result.stdout or result.stderr else "No output"
        
        return success, output
        
    except subprocess.TimeoutExpired:
        return False, "Verus timed out after 30 seconds"
    except Exception as e:
        return False, f"Error running verus: {e}"

def create_yaml_without_helpers(yaml_content: str) -> str:
    """Create a modified YAML with empty vc-helpers section."""
    lines = yaml_content.split('\n')
    result_lines = []
    in_helpers = False
    
    for line in lines:
        if line.startswith('vc-helpers:'):
            result_lines.append(line)
            result_lines.append('')  # Empty helpers section
            in_helpers = True
        elif line.startswith('vc-spec:') and in_helpers:
            # End of helpers section, start of spec section
            result_lines.append(line)
            in_helpers = False
        elif not in_helpers:
            result_lines.append(line)
        # Skip lines that are part of vc-helpers content
    
    return '\n'.join(result_lines)

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
    
    # Find verus executable
    verus_cmd = find_verus_executable()
    if not verus_cmd:
        print("❌ Verus executable not found. Please install verus or add it to PATH.")
        print("   Try: cargo install --git https://github.com/verus-lang/verus verus")
        return 1
    
    print(f"✅ Found Verus at: {verus_cmd}")
    
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