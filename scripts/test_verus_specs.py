#!/usr/bin/env python3

import subprocess
from pathlib import Path
import sys

# Directory paths
SPEC_DIR = Path("/Users/sergiu.bursuc/baif/vericoding/benchmarks/verus/humaneval/spec")

def test_verus_file(spec_file: Path) -> tuple[bool, str]:
    """Test a single Verus spec file."""
    try:
        # Run verus on the file
        result = subprocess.run(
            ["verus", str(spec_file)],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            return True, "✓ Verified successfully"
        else:
            return False, f"✗ Verification failed: {result.stderr.strip()}"
            
    except subprocess.TimeoutExpired:
        return False, "✗ Timeout (30s)"
    except FileNotFoundError:
        return False, "✗ Verus not found (check VERUS_PATH)"
    except Exception as e:
        return False, f"✗ Error: {e}"

def main():
    """Test all Verus spec files."""
    print("=== Testing Verus Spec Files ===")
    
    if not SPEC_DIR.exists():
        print(f"Error: Spec directory not found: {SPEC_DIR}")
        return
    
    # Get all .rs files
    spec_files = list(SPEC_DIR.glob("*.rs"))
    print(f"Found {len(spec_files)} spec files to test")
    
    if not spec_files:
        print("No spec files found!")
        return
    
    # Test each file
    passed = 0
    failed = 0
    
    for spec_file in sorted(spec_files):
        print(f"\nTesting {spec_file.name}...")
        success, message = test_verus_file(spec_file)
        
        if success:
            passed += 1
            print(f"  {message}")
        else:
            failed += 1
            print(f"  {message}")
            # Show first few lines of error for context
            if "Verification failed:" in message:
                error_lines = message.split('\n')[:3]
                for line in error_lines:
                    if line.strip():
                        print(f"    {line.strip()}")
    
    print(f"\n=== Summary ===")
    print(f"✓ Passed: {passed}")
    print(f"✗ Failed: {failed}")
    print(f"Total: {len(spec_files)}")
    
    if failed == 0:
        print("🎉 All spec files verified successfully!")
    else:
        print(f"⚠️  {failed} files need attention")

if __name__ == "__main__":
    main()
