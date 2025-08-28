#!/usr/bin/env python3
"""
Script to copy Lean files from NumpyHoareTriple subdirectories to numpy_all directory.

For each file YYY.lean in a nested subfolder path XXX/ZZZ/... of NumpyHoareTriple/, 
copy the file to numpy_all/ and rename it XXX_ZZZ_..._YYY.lean.
Only copies files from subfolders, not from the top-level directory.
Ignores files in the 'testing' and 'typing' folders.
"""

import os
import shutil
from pathlib import Path
import argparse


def copy_and_rename_files(source_dir: str, target_dir: str, dry_run: bool = False) -> None:
    """
    Copy Lean files from subdirectories (including nested) of source_dir to target_dir with renamed files.
    Only copies files from subfolders, not from the top-level directory.
    Ignores files in the 'testing' and 'typing' folders.
    
    Args:
        source_dir: Source directory containing subdirectories with .lean files
        target_dir: Target directory where files will be copied and renamed
        dry_run: If True, only print what would be done without actually copying
    """
    source_path = Path(source_dir)
    target_path = Path(target_dir)
    
    if not source_path.exists():
        print(f"Error: Source directory '{source_dir}' does not exist")
        return
    
    # Create target directory if it doesn't exist
    if not dry_run:
        target_path.mkdir(parents=True, exist_ok=True)
        print(f"Created target directory: {target_path}")
    else:
        print(f"Would create target directory: {target_path}")
    
    copied_count = 0
    skipped_count = 0
    
    # Find all .lean files recursively in the source directory
    all_lean_files = list(source_path.rglob("*.lean"))
    
    if not all_lean_files:
        print("No .lean files found in source directory")
        return
    
    # Filter out files that are directly in the source directory (not in subfolders)
    # and files in the 'testing' and 'typing' folders
    subfolder_files = []
    for lean_file in all_lean_files:
        rel_path = lean_file.relative_to(source_path)
        # Only include files that have a parent directory (i.e., are in subfolders)
        # and are not in the 'testing' or 'typing' folders
        if rel_path.parent != Path('.') and 'testing' not in rel_path.parts and 'typing' not in rel_path.parts:
            subfolder_files.append(lean_file)
    
    if not subfolder_files:
        print("No .lean files found in subfolders (excluding testing and typing folders)")
        return
    
    print(f"Found {len(subfolder_files)} .lean files in subfolders to process (excluding testing and typing folders)")
    
    # Group files by their relative path for better organization
    files_by_path = {}
    for lean_file in subfolder_files:
        # Get relative path from source directory
        rel_path = lean_file.relative_to(source_path)
        parent_dir = rel_path.parent
        
        if parent_dir not in files_by_path:
            files_by_path[parent_dir] = []
        files_by_path[parent_dir].append(lean_file)
    
    # Process files grouped by their path
    for parent_dir, lean_files in sorted(files_by_path.items()):
        print(f"\nProcessing subdirectory: {parent_dir}")
        
        for lean_file in lean_files:
            # Create new filename by joining the path components with underscores
            rel_path = lean_file.relative_to(source_path)
            path_parts = list(rel_path.parent.parts) + [lean_file.stem]
            
            # Join all path components with underscores and add .lean extension
            new_filename = "_".join(path_parts) + ".lean"
            target_file = target_path / new_filename
            
            if target_file.exists() and not dry_run:
                print(f"  WARNING: Target file already exists, skipping: {new_filename}")
                skipped_count += 1
                continue
                
            if dry_run:
                print(f"  Would copy: {lean_file} -> {target_file}")
            else:
                try:
                    shutil.copy2(lean_file, target_file)
                    print(f"  Copied: {lean_file.name} -> {new_filename}")
                    copied_count += 1
                except Exception as e:
                    print(f"  ERROR copying {lean_file.name}: {e}")
                    skipped_count += 1
    
    # Summary
    print(f"\n{'DRY RUN - ' if dry_run else ''}Summary:")
    print(f"  Files copied: {copied_count}")
    print(f"  Files skipped: {skipped_count}")
    print(f"  Total processed: {copied_count + skipped_count}")


def main():
    parser = argparse.ArgumentParser(
        description="Copy Lean files from NumpyHoareTriple subdirectories to numpy_all directory"
    )
    parser.add_argument(
        "--source", 
        default="lean/NumpyHoareTriple",
        help="Source directory (default: lean/NumpyHoareTriple)"
    )
    parser.add_argument(
        "--target", 
        default="benchmarks/lean/numpy_all",
        help="Target directory (default: benchmarks/lean/numpy_all)"
    )
    parser.add_argument(
        "--dry-run", 
        action="store_true",
        help="Show what would be done without actually copying files"
    )
    
    args = parser.parse_args()
    
    print(f"Source directory: {args.source}")
    print(f"Target directory: {args.target}")
    if args.dry_run:
        print("DRY RUN MODE - No files will be copied")
    
    copy_and_rename_files(args.source, args.target, args.dry_run)


if __name__ == "__main__":
    main()
