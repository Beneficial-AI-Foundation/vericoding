#!/usr/bin/env python3
"""
Script to replace files in numpy_all/ with corresponding files from numpy_replace_new/
if they match the contents in numpy_replace_old/.
"""

import os
import shutil
import filecmp
from pathlib import Path

def main():
    # Define the directory paths
    triple_dir = Path("benchmarks/lean/numpy_all")
    old_dir = Path("benchmarks/.stash/numpy_replace_old")
    new_dir = Path("benchmarks/.stash/numpy_replace_new")
    
    # Check if directories exist
    if not triple_dir.exists():
        print(f"Error: {triple_dir} does not exist")
        return
    
    if not old_dir.exists():
        print(f"Error: {old_dir} does not exist")
        return
    
    if not new_dir.exists():
        print(f"Error: {new_dir} does not exist")
        return
    
    # Get all files in numpy_all
    triple_files = list(triple_dir.glob("*.lean"))
    
    print(f"Found {len(triple_files)} files in {triple_dir}")
    
    replaced_count = 0
    skipped_count = 0
    error_count = 0
    
    for triple_file in triple_files:
        filename = triple_file.name
        old_file = old_dir / filename
        new_file = new_dir / filename
        
        print(f"\nProcessing: {filename}")
        
        # Check if file exists in old directory
        if not old_file.exists():
            print(f"  Skipped: {filename} not found in {old_dir}")
            skipped_count += 1
            continue
        
        # Check if file exists in new directory
        if not new_file.exists():
            print(f"  Error: {filename} not found in {new_dir}")
            error_count += 1
            continue
        
        # Compare triple file with old file
        try:
            if filecmp.cmp(triple_file, old_file, shallow=False):
                print(f"  Match found! Replacing {filename}")
                
                # Create backup
                backup_file = triple_file.with_suffix(triple_file.suffix + ".backup")
                shutil.copy2(triple_file, backup_file)
                print(f"    Backup created: {backup_file}")
                
                # Replace with new file
                shutil.copy2(new_file, triple_file)
                print(f"    Replaced with: {new_file}")
                
                replaced_count += 1
            else:
                # print(f"  Skipped: {filename} contents differ from {old_dir}")
                skipped_count += 1
                
        except Exception as e:
            print(f"  Error comparing {filename}: {e}")
            error_count += 1
    
    # Summary
    print(f"\n{'='*50}")
    print(f"Summary:")
    print(f"  Files processed: {len(triple_files)}")
    print(f"  Files replaced: {replaced_count}")
    print(f"  Files skipped: {skipped_count}")
    print(f"  Errors: {error_count}")
    print(f"{'='*50}")

if __name__ == "__main__":
    main()
