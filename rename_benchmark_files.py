#!/usr/bin/env python3
"""
Script to rename benchmark files based on the mapping in vericoding_benchmark_v1.jsonl.

This script renames files in the format ZZZ.dfy, ZZZ.lean, or ZZZ.rs in the 
benchmarks/XXX/YYY/tasks and benchmarks/XXX/YYY/issues folders according to the 
mapping provided in the JSONL file.

Example: apps_test_5.dfy -> DA0001.dfy (if the mapping shows source-id: "apps_test_5" -> id: "DA0001")
"""

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Tuple


def load_mapping(jsonl_file: str) -> Dict[str, str]:
    """
    Load the mapping from source-id to id from the JSONL file.
    
    Args:
        jsonl_file: Path to the JSONL file
        
    Returns:
        Dictionary mapping source-id to id
    """
    mapping = {"lean": {}, "dafny": {}, "verus": {}}
    
    with open(jsonl_file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                data = json.loads(line)
                source_id = data.get('source-id')
                new_id = data.get('id')
                language = data.get('language')
                if source_id and new_id and language:
                    mapping[language][source_id] = new_id
    
    return mapping


def find_benchmark_files(base_dir: str) -> List[Tuple[str, str, str]]:
    """
    Find all benchmark files that need to be renamed.
    
    Args:
        base_dir: Base directory containing the benchmarks
        
    Returns:
        List of tuples (file_path, source_id, extension, language)
    """
    files_to_rename = []
    base_path = Path(base_dir)
    
    # Look for files in benchmarks/XXX/YYY/tasks and benchmarks/XXX/YYY/issues
    for language_dir in base_path.iterdir():
        if not language_dir.is_dir() or language_dir.name in ['README.md', 'vericoding_benchmark_v1.csv', 'vericoding_benchmark_v1.jsonl']:
            continue
        language = language_dir.name
        for source_dir in language_dir.iterdir():
            if not source_dir.is_dir():
                continue
                
            # Check both tasks and issues directories
            for subdir in ['tasks', 'issues']:
                subdir_path = source_dir / subdir
                if subdir_path.exists() and subdir_path.is_dir():
                    for file_path in subdir_path.iterdir():
                        if file_path.is_file():
                            # Check if file matches the pattern ZZZ.dfy, ZZZ.lean, or ZZZ.rs
                            match = re.match(r'^(.+)\.(dfy|lean|rs)$', file_path.name)
                            if match:
                                source_id = match.group(1)
                                extension = match.group(2)
                                files_to_rename.append((str(file_path), source_id, extension, language))
    
    return files_to_rename


def rename_files(files_to_rename: List[Tuple[str, str, str, str]], mapping: Dict[str, str], dry_run: bool = True) -> None:
    """
    Rename files according to the mapping.
    
    Args:
        files_to_rename: List of files to rename
        mapping: Dictionary mapping source-id to new id for each language
        dry_run: If True, only print what would be done without actually renaming
    """
    renamed_count = 0
    not_found_count = 0
    
    print(f"{'DRY RUN: ' if dry_run else ''}Renaming files...")
    print("-" * 60)
    
    for file_path, source_id, extension, language in files_to_rename:
        if source_id in mapping[language]:
            new_id = mapping[language][source_id]
            new_filename = f"{new_id}.{extension}"
            new_file_path = os.path.join(os.path.dirname(file_path), new_filename)
            
            if dry_run:
                print(f"Would rename: {os.path.basename(file_path)} -> {new_filename}")
            else:
                try:
                    os.rename(file_path, new_file_path)
                    print(f"Renamed: {os.path.basename(file_path)} -> {new_filename}")
                except OSError as e:
                    print(f"Error renaming {file_path}: {e}")
                    continue
            
            renamed_count += 1
        else:
            print(f"Warning: No mapping found for source-id '{source_id}' in file {file_path}")
            not_found_count += 1
    
    print("-" * 60)
    print(f"Summary:")
    print(f"  Files renamed: {renamed_count}")
    print(f"  Files without mapping: {not_found_count}")
    print(f"  Total files processed: {len(files_to_rename)}")


def main():
    """Main function to execute the renaming script."""
    # Configuration
    base_dir = "/home/shaowei/projects/vericoding/benchmarks"
    jsonl_file = os.path.join(base_dir, "vericoding_benchmark_v1.jsonl")
    
    print("Benchmark File Renaming Script")
    print("=" * 40)
    
    # Check if JSONL file exists
    if not os.path.exists(jsonl_file):
        print(f"Error: JSONL file not found at {jsonl_file}")
        return
    
    # Load the mapping
    print("Loading mapping from JSONL file...")
    mapping = load_mapping(jsonl_file)
    print(f"Loaded {len(mapping)} mappings")
    
    # Find files to rename
    print("Finding benchmark files...")
    files_to_rename = find_benchmark_files(base_dir)
    print(f"Found {len(files_to_rename)} files to potentially rename")
    
    if not files_to_rename:
        print("No files found to rename.")
        return
    
    # Show some examples
    print("\nExample files found:")
    for i, (file_path, source_id, extension, language) in enumerate(files_to_rename[:5]):
        new_id = mapping[language].get(source_id, "NO_MAPPING")
        print(f"  {os.path.basename(file_path)} -> {new_id}.{extension}")
    if len(files_to_rename) > 5:
        print(f"  ... and {len(files_to_rename) - 5} more files")
    
    # Ask for confirmation
    print(f"\nFound {len(files_to_rename)} files to process.")
    print("This script will rename files according to the mapping in the JSONL file.")
    
    # First, do a dry run
    print("\n" + "="*60)
    print("DRY RUN - Showing what would be renamed:")
    rename_files(files_to_rename, mapping, dry_run=True)
    
    # Ask for confirmation to proceed
    print("\n" + "="*60)
    response = input("Do you want to proceed with the actual renaming? (y/N): ").strip().lower()
    
    if response in ['y', 'yes']:
        print("\nProceeding with actual renaming...")
        rename_files(files_to_rename, mapping, dry_run=False)
        print("Renaming completed!")
    else:
        print("Renaming cancelled.")


if __name__ == "__main__":
    main()
