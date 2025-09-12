#!/usr/bin/env python3
"""
Check what code was generated and where it's located.
"""

import os
from pathlib import Path

def check_generated_files():
    """Check for generated code files."""
    
    print("Checking for generated code files...")
    print("=" * 50)
    
    # Check common output directories
    possible_dirs = [
        "generated_hoare_code",
        "generated_code", 
        "output",
        "results",
        ".",
    ]
    
    found_files = []
    
    for dir_name in possible_dirs:
        dir_path = Path(dir_name)
        if dir_path.exists() and dir_path.is_dir():
            print(f"\n📁 Checking directory: {dir_path.absolute()}")
            
            # Look for .lean files
            lean_files = list(dir_path.glob("*.lean"))
            if lean_files:
                print(f"  Found {len(lean_files)} .lean files:")
                for file_path in lean_files:
                    size = file_path.stat().st_size
                    print(f"    ✅ {file_path.name} ({size:,} bytes)")
                    found_files.append(file_path)
            else:
                print(f"  No .lean files found")
            
            # Look for other generated files
            other_files = [f for f in dir_path.iterdir() if f.is_file() and f.suffix != '.lean']
            if other_files:
                print(f"  Other files found:")
                for file_path in other_files:
                    size = file_path.stat().st_size
                    print(f"    📄 {file_path.name} ({size:,} bytes)")
    
    if not found_files:
        print(f"\n❌ No generated .lean files found in any directory")
        print(f"Possible reasons:")
        print(f"1. The generation script didn't run successfully")
        print(f"2. No API key was set")
        print(f"3. Files were saved to a different location")
        print(f"4. The response wasn't parsed correctly")
    else:
        print(f"\n✅ Found {len(found_files)} generated .lean files")
        
        # Show content of first file as example
        if found_files:
            first_file = found_files[0]
            print(f"\n📖 Example content from {first_file.name}:")
            try:
                with open(first_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                    print(f"Length: {len(content)} characters")
                    print(f"Preview:")
                    print("-" * 40)
                    print(content[:500] + "..." if len(content) > 500 else content)
                    print("-" * 40)
            except Exception as e:
                print(f"Error reading file: {e}")

def check_recent_output():
    """Check for any recent output or logs."""
    
    print(f"\n🔍 Checking for recent output...")
    print("=" * 50)
    
    # Check for any files modified in the last hour
    current_dir = Path(".")
    recent_files = []
    
    for file_path in current_dir.iterdir():
        if file_path.is_file():
            # Check if modified in last hour
            mtime = file_path.stat().st_mtime
            import time
            if time.time() - mtime < 3600:  # 1 hour
                recent_files.append(file_path)
    
    if recent_files:
        print(f"Files modified in the last hour:")
        for file_path in recent_files:
            size = file_path.stat().st_size
            print(f"  📄 {file_path.name} ({size:,} bytes)")
    else:
        print(f"No recently modified files found")

def main():
    """Main function to check generated code."""
    
    print("Check Generated Code")
    print("=" * 50)
    
    check_generated_files()
    check_recent_output()
    
    print(f"\n💡 To generate code, run:")
    print(f"   python3 generate_and_save_hoare_code.py")
    print(f"   (Make sure ANTHROPIC_API_KEY is set)")

if __name__ == "__main__":
    main()






















