#!/usr/bin/env python3
"""
Script to extract metadata about files in the benchmarks directory.

For each folder YYY of each folder XXX of `benchmarks`, this script:
1. Creates an empty object `files_meta`
2. Gets a list of all the files in `benchmarks/XXX/YYY/yaml` and validates they are .yaml files
3. For each file "ZZZ.yaml" in `benchmarks/XXX/YYY/yaml`, checks if "ZZZ" is a key in `files_meta`
4. If not, creates the key with an empty object as value
5. Inserts the key-value (XXX, 1) to V
6. Checks if "source" is a key of V and validates consistency
"""

import os
import sys
from pathlib import Path
from typing import Dict, Any

def get_files_meta(benchmarks_dir: Path) -> Dict[str, Any]:
    """Get metadata about files in the benchmarks directory."""

    # Initialize the main metadata object
    files_meta: Dict[str, Any] = {}
    
    # Iterate through each XXX folder (lean, dafny, verus)
    for xxx_dir in benchmarks_dir.iterdir():
        if not xxx_dir.is_dir() or xxx_dir.name.startswith('.'):
            continue
            
        xxx_name = xxx_dir.name
        print(f"Processing {xxx_name} directory...")
        
        # Iterate through each YYY subfolder
        for yyy_dir in xxx_dir.iterdir():
            if not yyy_dir.is_dir() or yyy_dir.name.startswith('.'):
                continue
                
            yyy_name = yyy_dir.name
            yaml_dir = yyy_dir / "yaml"
            
            # Check if yaml directory exists
            if not yaml_dir.exists():
                print(f"Warning: No yaml directory found in {yyy_dir}")
                continue
                
            if not yaml_dir.is_dir():
                raise NotADirectoryError(f"{yaml_dir} is not a directory")
            
            print(f"  Processing {yyy_name} subdirectory...")
            
            # Get all files in the yaml directory
            yaml_files = list(yaml_dir.iterdir())
            
            # Validate that all files are .yaml files
            for file_path in yaml_files:
                if not file_path.is_file():
                    raise ValueError(f"{file_path} is not a file")
                if not file_path.name.endswith('.yaml'):
                    raise ValueError(f"{file_path} is not a .yaml file")
                if ' ' in file_path.name:
                    raise ValueError(f"{file_path} contains spaces in filename")
            
            # Process each YAML file
            for yaml_file in yaml_files:
                # Extract the base name (ZZZ) from ZZZ.yaml
                zzz_name = yaml_file.stem  # This removes the .yaml extension
                
                # Check if ZZZ is a key in files_meta
                if zzz_name not in files_meta:
                    files_meta[zzz_name] = {}
                
                v = files_meta[zzz_name]
                
                # Insert the key-value (XXX, 1) to V
                v[xxx_name] = 1
                
                # Check if "source" is a key of V
                if "source" in v:
                    if v["source"] != yyy_name:
                        raise ValueError(f"Inconsistent source for {zzz_name}. "
                                       f"Expected {v['source']}, found {yyy_name}")
                else:
                    # Insert the key-value ("source", YYY) to V
                    v["source"] = yyy_name

    return files_meta

def get_all_sources(files_meta: Dict[str, Any]) -> set[str]:
    """Get all possible sources from files_meta.
    
    Args:
        files_meta: Dictionary containing file metadata
        
    Returns:
        Set of all unique source values found in files_meta
    """
    sources = set()
    for file_data in files_meta.values():
        if "source" in file_data:
            sources.add(file_data["source"])
    return sources

def count_files_by_source(files_meta: Dict[str, Any]) -> Dict[str, Dict[str, int]]:
    """Count files by source and language type.
    
    For each source in files_meta, counts:
    1. Total number of filenames with that source
    2. Total number of Lean filenames with that source
    3. Total number of Dafny filenames with that source
    4. Total number of Verus filenames with that source
    
    Args:
        files_meta: Dictionary containing file metadata
        
    Returns:
        Dictionary mapping source names to counts of different file types
    """
    source_counts = {}
    
    for filename, file_data in files_meta.items():
        source = file_data.get("source")
        if source is None:
            continue
            
        # Initialize source entry if not exists
        if source not in source_counts:
            source_counts[source] = {
                "total": 0,
                "lean": 0,
                "dafny": 0,
                "verus": 0
            }
        
        # Count total files for this source
        source_counts[source]["total"] += 1
        
        # Count files by language type
        if "lean" in file_data:
            source_counts[source]["lean"] += 1
        if "dafny" in file_data:
            source_counts[source]["dafny"] += 1
        if "verus" in file_data:
            source_counts[source]["verus"] += 1
    
    return source_counts

def validate_source_signatures(files_meta: Dict[str, Any]) -> None:
    """Validate that all entries for each source have the same signature.
    
    For each source, filters out all entries from files_meta with that source,
    then checks that all the filtered entries have the same (Lean, Verus, Dafny) signature.
    Prints out all files with inconsistent signatures.
    
    Args:
        files_meta: Dictionary containing file metadata
    """
    sources = get_all_sources(files_meta)
    inconsistent_files = []
    
    for source in sources:
        # Filter entries for this source
        source_entries = {
            filename: data for filename, data in files_meta.items()
            if data.get("source") == source
        }
        
        if not source_entries:
            continue
            
        # Get the signature (set of languages) for the first entry
        first_entry = next(iter(source_entries.values()))
        expected_signature = set(key for key in first_entry.keys() if key != "source")
        
        # Check that all other entries have the same signature
        for filename, entry_data in source_entries.items():
            entry_signature = set(key for key in entry_data.keys() if key != "source")
            if entry_signature != expected_signature:
                inconsistent_files.append({
                    'source': source,
                    'filename': filename,
                    'actual_signature': sorted(entry_signature),
                    'expected_signature': sorted(expected_signature)
                })
    
    # Print all inconsistent files
    if inconsistent_files:
        print("\nFiles with inconsistent signatures:")
        print("=" * 50)
        for item in inconsistent_files:
            print(f"Source: {item['source']} File: {item['filename']} {item['expected_signature']} {item['actual_signature']}")
    else:
        print("\nAll files have consistent signatures for their sources.")

def main():
    """Main function to extract metadata from benchmarks directory."""
    benchmarks_dir = Path("/home/shaowei/projects/vericoding/benchmarks")
    
    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")
    
    files_meta = get_files_meta(benchmarks_dir)
    
    print(f"\nTotal files processed: {len(files_meta)}")
    
    # Optionally save to a file
    import json
    output_file = benchmarks_dir / "generated_metadata.json"
    with open(output_file, 'w') as f:
        json.dump(files_meta, f, indent=2, sort_keys=True)
    
    print(f"Metadata saved to: {output_file}")

    # Validate that all entries for each source have consistent signatures
    validate_source_signatures(files_meta)
    
    # Count files by source and language type
    source_counts = count_files_by_source(files_meta)
    
    print("\nFile counts by source:")
    print("=" * 50)
    for source, counts in sorted(source_counts.items()):
        print(f"Source: {source}")
        print(f"  Total files: {counts['total']}")
        print(f"  Lean files: {counts['lean']}")
        print(f"  Dafny files: {counts['dafny']}")
        print(f"  Verus files: {counts['verus']}")
        print()
    


if __name__ == "__main__":
    main()
