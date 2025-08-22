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
        shutil.copy2(yaml_path, temp_yaml)
        
        result = subprocess.run([
            "uv", "run", "src/convert_from_yaml.py",
            str(temp_yaml),
            "--suffix", "rs"
        ], capture_output=True, text=True, cwd=Path(__file__).parent.parent)
        
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
    project_root = Path(__file__).parent.parent
    tests_dir = project_root / "tests"
    
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
        
        for yaml_file in yaml_files:
            print(f"\n🔄 Testing {yaml_file.name}...")
            
            # Step 1: Convert YAML to Rust in temp directory
            print(f"   Converting to Rust...")
            success, temp_rust_file = convert_yaml_to_rust(yaml_file, temp_path)
            if not success:
                results.append((yaml_file.name, False, "Conversion failed"))
                continue
            
            # Step 2: Verify with Verus --no-verify (syntax check)
            print(f"   Running Verus syntax check...")
            success, output = verify_rust_with_verus(temp_rust_file, verus_cmd)
            
            if success:
                print(f"   ✅ Verus syntax check passed")
                results.append((yaml_file.name, True, "Success"))
            else:
                print(f"   ❌ Verus syntax check failed")
                print(f"   Output: {output}")
                results.append((yaml_file.name, False, f"Verus failed: {output}"))
    
    # Print summary
    print(f"\n📊 Test Results Summary:")
    print(f"=" * 50)
    
    passed = 0
    failed = 0
    
    for filename, success, message in results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {filename}")
        if not success:
            print(f"      {message[:100]}{'...' if len(message) > 100 else ''}")
        
        if success:
            passed += 1
        else:
            failed += 1
    
    print(f"\n🏁 Final Results:")
    print(f"   Passed: {passed}")
    print(f"   Failed: {failed}")
    print(f"   Total:  {len(results)}")
    
    if failed == 0:
        print(f"\n🎉 All tests passed! YAML roundtrip with Verus syntax check successful.")
        return 0
    else:
        print(f"\n💥 {failed} tests failed. Check output above for details.")
        return 1

if __name__ == "__main__":
    sys.exit(main())