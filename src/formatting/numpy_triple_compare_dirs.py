#!/usr/bin/env python3
"""
Script to compare numpy and numpy_triple directories and identify missing files.

This script compares the files in benchmarks/lean/numpy/ and benchmarks/lean/numpy_triple/
to identify which files are missing from each directory.
"""

import os
from pathlib import Path
import argparse
from collections import defaultdict


def get_lean_files(directory: str) -> set:
    """
    Get all .lean files from a directory.
    
    Args:
        directory: Path to the directory to scan
        
    Returns:
        Set of .lean filenames
    """
    dir_path = Path(directory)
    if not dir_path.exists():
        print(f"Warning: Directory '{directory}' does not exist")
        return set()
    
    lean_files = set()
    for file_path in dir_path.glob("*.lean"):
        lean_files.add(file_path.name)
    
    return lean_files


def compare_directories(dir1: str, dir2: str, verbose: bool = False) -> dict:
    """
    Compare two directories and identify differences.
    
    Args:
        dir1: First directory path
        dir2: Second directory path  
        verbose: Whether to print detailed information
        
    Returns:
        Dictionary with comparison results
    """
    files1 = get_lean_files(dir1)
    files2 = get_lean_files(dir2)
    
    if verbose:
        print(f"Files in {dir1}: {len(files1)}")
        print(f"Files in {dir2}: {len(files2)}")
    
    # Files in dir1 but not in dir2
    missing_in_dir2 = files1 - files2
    
    # Files in dir2 but not in dir1
    missing_in_dir1 = files2 - files1
    
    # Files in both directories
    common_files = files1 & files2
    
    return {
        'dir1': dir1,
        'dir2': dir2,
        'files_in_dir1': len(files1),
        'files_in_dir2': len(files2),
        'missing_in_dir2': missing_in_dir2,
        'missing_in_dir1': missing_in_dir1,
        'common_files': common_files,
        'total_common': len(common_files)
    }


def group_files_by_category(files: set) -> dict:
    """
    Group files by their category (prefix before underscore).
    
    Args:
        files: Set of filenames
        
    Returns:
        Dictionary mapping categories to lists of files
    """
    categories = defaultdict(list)
    
    for filename in sorted(files):
        if '_' in filename:
            category = filename.split('_')[0]
            categories[category].append(filename)
        else:
            categories['other'].append(filename)
    
    return dict(categories)


def print_missing_files(title: str, missing_files: set, verbose: bool = False):
    """
    Print missing files in a formatted way.
    
    Args:
        title: Title for the section
        missing_files: Set of missing filenames
        verbose: Whether to print detailed file lists
    """
    print(f"\n{title} ({len(missing_files)})")
    print("=" * (len(title) + len(str(len(missing_files))) + 3))
    
    if missing_files:
        if verbose:
            # Group by category and show all files
            categories = group_files_by_category(missing_files)
            for category, files in sorted(categories.items()):
                print(f"\n{category} ({len(files)} files):")
                for file in files:
                    print(f"  - {file}")
        else:
            # Just show categories and counts
            categories = group_files_by_category(missing_files)
            for category, files in sorted(categories.items()):
                print(f"  {category}: {len(files)} files")
                if len(files) <= 5:  # Show individual files if there are 5 or fewer
                    for file in files:
                        print(f"    - {file}")
    else:
        print("  No files missing!")


def print_comparison_results(results: dict, verbose: bool = False):
    """
    Print the comparison results in a formatted way.
    
    Args:
        results: Dictionary with comparison results
        verbose: Whether to print detailed file lists
    """
    print(f"\n=== Directory Comparison Results ===")
    print(f"Directory 1: {results['dir1']}")
    print(f"Directory 2: {results['dir2']}")
    print(f"Files in Directory 1: {results['files_in_dir1']}")
    print(f"Files in Directory 2: {results['files_in_dir2']}")
    print(f"Common files: {results['total_common']}")
    
    # Files missing in dir2 (files that exist in dir1 but not in dir2)
    missing_in_dir2 = results['missing_in_dir2']
    print_missing_files(
        f"Files in {results['dir1']} but missing in {results['dir2']}", 
        missing_in_dir2, 
        verbose
    )
    
    # Files missing in dir1 (files that exist in dir2 but not in dir1)
    missing_in_dir1 = results['missing_in_dir1']
    print_missing_files(
        f"Files in {results['dir2']} but missing in {results['dir1']}", 
        missing_in_dir1, 
        verbose
    )
    
    # Summary
    print(f"\n=== Summary ===")
    print(f"Total files in {results['dir1']}: {results['files_in_dir1']}")
    print(f"Total files in {results['dir2']}: {results['files_in_dir2']}")
    print(f"Files missing in {results['dir2']}: {len(missing_in_dir2)}")
    print(f"Files missing in {results['dir1']}: {len(missing_in_dir1)}")
    print(f"Common files: {results['total_common']}")
    
    # Additional insights
    if len(missing_in_dir2) > 0:
        print(f"\n💡 To sync {results['dir2']} with {results['dir1']}, copy {len(missing_in_dir2)} files")
    if len(missing_in_dir1) > 0:
        print(f"💡 To sync {results['dir1']} with {results['dir2']}, copy {len(missing_in_dir1)} files")
    if len(missing_in_dir2) == 0 and len(missing_in_dir1) == 0:
        print(f"\n✅ Both directories are in sync!")


def main():
    parser = argparse.ArgumentParser(
        description="Compare numpy and numpy_triple directories"
    )
    parser.add_argument(
        "--dir1", 
        default="benchmarks/lean/numpy",
        help="First directory to compare (default: benchmarks/lean/numpy)"
    )
    parser.add_argument(
        "--dir2", 
        default="benchmarks/lean/numpy_triple",
        help="Second directory to compare (default: benchmarks/lean/numpy_triple)"
    )
    parser.add_argument(
        "--verbose", 
        action="store_true",
        help="Show detailed file lists"
    )
    
    args = parser.parse_args()
    
    print(f"Comparing directories:")
    print(f"  Directory 1: {args.dir1}")
    print(f"  Directory 2: {args.dir2}")
    
    results = compare_directories(args.dir1, args.dir2, args.verbose)
    print_comparison_results(results, args.verbose)


if __name__ == "__main__":
    main()
