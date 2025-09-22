#!/usr/bin/env python3
"""
Script to extract metadata about files in the benchmarks directory.

For each folder YYY of each folder XXX of `benchmarks`, this script:
1. Creates an empty object `source_meta`
2. Gets a list of all the files in `benchmarks/XXX/YYY/yaml` and validates they are .yaml files
3. For each file "ZZZ.yaml" in `benchmarks/XXX/YYY/yaml`, checks if "ZZZ" is a key in `source_meta`
4. If not, creates the key with an empty object as value
5. Inserts the key-value (XXX, 1) to V
6. Checks if "source" is a key of V and validates consistency
"""

import os
import sys
import json
from pathlib import Path
from typing import Dict, Any

def get_source_meta(benchmarks_dir: Path, save_path: Path = None) -> Dict[str, Any]:
    """Get metadata about files in the benchmarks directory."""

    # Initialize the main metadata object
    if save_path and save_path.exists():
        with open(save_path, 'r') as f:
            source_meta = json.load(f)
    else:
        source_meta = {}

    source_meta: Dict[str, Any] = {}
    
    # Iterate through each XXX folder (lean, dafny, verus)
    for xxx_dir in benchmarks_dir.iterdir():
        if not xxx_dir.is_dir() or xxx_dir.name.startswith('.'):
            continue
            
        xxx_name = xxx_dir.name
        if xxx_name not in ["lean", "dafny", "verus"]:
            raise ValueError(f"Unknown benchmark type '{xxx_name}'. Expected 'lean', 'dafny', or 'verus'.")
        # print(f"Processing {xxx_name} directory...")
        
        # Iterate through each YYY subfolder
        for yyy_dir in xxx_dir.iterdir():
            if not yyy_dir.is_dir() or yyy_dir.name.startswith('.'):
                continue
                
            yyy_name = yyy_dir.name

            # Validate that the YYY subdirectory is either "poor", "yaml", or "files"
            for yyy_subdir in yyy_dir.iterdir():
                if not yyy_subdir.is_dir() or yyy_subdir.name.startswith('.'):
                    continue
                    
                yyy_subdir_name = yyy_subdir.name
                if yyy_subdir_name not in ["poor","yaml","files"]:
                    raise ValueError(f"Unknown benchmark type '{yyy_subdir_name}' in {yyy_dir}. Expected 'poor' or 'yaml' or 'files'.")
        
            yaml_dir = yyy_dir / "yaml"
            poor_dir = yyy_dir / "poor"
            
            # Check if yaml directory exists
            if not yaml_dir.exists():
                print(f"Warning: No yaml directory found in {yyy_dir}")
                continue
                
            if not yaml_dir.is_dir():
                raise NotADirectoryError(f"{yaml_dir} is not a directory")
            
            # print(f"  Processing {yyy_name} subdirectory...")
            
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
                
                # Check if ZZZ is a key in source_meta
                if zzz_name not in source_meta:
                    # Initialize SM[XXX][YYY] = "" for YYY in [Lean, Dafny, Verus]
                    source_meta[zzz_name] = {
                        "lean": "",
                        "dafny": "",
                        "verus": ""
                    }
                
                v = source_meta[zzz_name]
                
                # Insert the key-value (XXX, "yaml") to V
                v[xxx_name] = "yaml"
                
                # Check if "source" is a key of V
                if "source" in v:
                    if v["source"] != yyy_name:
                        raise ValueError(f"Inconsistent source for {zzz_name}. "
                                       f"Expected {v['source']}, found {yyy_name}")
                else:
                    # Insert the key-value ("source", YYY) to V
                    v["source"] = yyy_name
            
            # Process poor directory if it exists
            if poor_dir.exists() and poor_dir.is_dir():
                # print(f"  Processing poor directory in {yyy_name}...")
                
                # Check for any files that are not directories and don't start with "."
                for item in poor_dir.iterdir():
                    if item.is_file() and not item.name.startswith('.'):
                        raise ValueError(f"Found unexpected file in poor directory: {item}. "
                                       f"Only directories are allowed in poor directory.")
                
                # Iterate through each ZZZ folder in poor directory
                for zzz_dir in poor_dir.iterdir():
                    if not zzz_dir.is_dir() or zzz_dir.name.startswith('.'):
                        continue
                    
                    zzz_name = zzz_dir.name
                    # print(f"    Processing poor/{zzz_name} folder...")
                    
                    # Get all files in the ZZZ folder
                    zzz_files = list(zzz_dir.iterdir())
                    for www_file in zzz_files:
                        if not www_file.is_file() or www_file.name.startswith('.'):
                            raise ValueError(f"Found unexpected file in poor directory: {www_file}. ")
                        if not www_file.name.endswith('.yaml'):
                            if zzz_dir.name not in ["unformatted"]:
                                raise ValueError(f"{www_file} in {zzz_dir} is not a .yaml file")

                        www_name = www_file.name
                        
                        # Case 1: WWW is of the form UUU.yaml
                        uuu_name = www_file.stem  # Remove .yaml extension
                        
                        # Check if UUU is already in source_meta
                        if uuu_name in source_meta:
                            # Raise error if SM[UUU][XXX] starts with "yaml"
                            if source_meta[uuu_name][xxx_name].startswith("yaml"):
                                raise ValueError(f"SM[{uuu_name}][{xxx_name}] starts with 'yaml' but file is poor; "
                                                f"path: {www_file}, "
                                                f"found: {source_meta[uuu_name][xxx_name]}")
                        else:
                            # Create entry SM[UUU] with empty strings for all languages
                            source_meta[uuu_name] = {
                                "lean": "",
                                "dafny": "",
                                "verus": ""
                            }
                        
                        # Set SM[UUU][XXX] to "poor/ZZZ"
                        source_meta[uuu_name][xxx_name] = f"poor/{zzz_name}"
                        
                        # Set source if not already set
                        if "source" not in source_meta[uuu_name]:
                            source_meta[uuu_name]["source"] = yyy_name
                        elif source_meta[uuu_name]["source"] != yyy_name:
                            raise ValueError(f"Inconsistent source for {uuu_name}. "
                                            f"Expected {source_meta[uuu_name]['source']}, found {yyy_name}")

    print(f"\nTotal files processed: {len(source_meta)}")

    source_meta = generate_ids(source_meta)
    
    if save_path:
        with open(save_path, 'w') as f:
            json.dump(source_meta, f, indent=2, sort_keys=True)
        print(f"Metadata saved to: {save_path}")

    return source_meta

def get_all_sources(source_meta: Dict[str, Any]) -> set[str]:
    """Get all possible sources from source_meta.
    
    Args:
        source_meta: Dictionary containing file metadata
        
    Returns:
        Set of all unique source values found in source_meta
    """
    sources = set()
    for file_data in source_meta.values():
        if "source" in file_data:
            sources.add(file_data["source"])
    return sources

def count_files_by_source(source_meta: Dict[str, Any]) -> Dict[str, Dict[str, int]]:
    """Count files by source and language type.
    
    For each source in source_meta, counts:
    1. Total number of filenames with that source
    2. Total number of Lean filenames with that source
    3. Total number of Dafny filenames with that source
    4. Total number of Verus filenames with that source
    
    Args:
        source_meta: Dictionary containing file metadata
        
    Returns:
        Dictionary mapping source names to counts of different file types
    """
    source_counts = {}
    
    for filename, file_data in source_meta.items():
        source = file_data.get("source")
        if source is None:
            continue
            
        # Initialize source entry if not exists
        if source not in source_counts:
            source_counts[source] = {
                "total": 0,
                "lean": {'yaml': 0, 'poor': 0},
                "dafny": {'yaml': 0, 'poor': 0},
                "verus": {'yaml': 0, 'poor': 0}
            }
        
        # Count total files for this source
        source_counts[source]["total"] += 1
        
        # Count files by language type (check for non-empty string values)
        if "lean" in file_data and file_data["lean"].startswith("yaml"):
            source_counts[source]["lean"]['yaml'] += 1
        if "dafny" in file_data and file_data["dafny"].startswith("yaml"):
            source_counts[source]["dafny"]['yaml'] += 1
        if "verus" in file_data and file_data["verus"].startswith("yaml"):
            source_counts[source]["verus"]['yaml'] += 1
        if "lean" in file_data and file_data["lean"].startswith("poor"):
            source_counts[source]["lean"]['poor'] += 1
        if "dafny" in file_data and file_data["dafny"].startswith("poor"):
            source_counts[source]["dafny"]['poor'] += 1
        if "verus" in file_data and file_data["verus"].startswith("poor"):
            source_counts[source]["verus"]['poor'] += 1
    
    return source_counts

def validate_source_signatures(source_meta: Dict[str, Any]) -> None:
    """Validate that all entries for each source have the same signature.
    
    For each source, filters out all entries from source_meta with that source,
    then checks that all the filtered entries have the same (Lean, Verus, Dafny) signature.
    Prints out all files with inconsistent signatures.
    
    Args:
        source_meta: Dictionary containing file metadata
    """
    sources = get_all_sources(source_meta)
    inconsistent_files = []
    
    for source in sources:
        # Filter entries for this source
        source_entries = {
            filename: data for filename, data in source_meta.items()
            if data.get("source") == source
        }
        
        if not source_entries:
            continue
            
        # Get the signature (set of languages with non-empty values) for the first entry
        first_entry = next(iter(source_entries.values()))
        expected_signature = set(key for key in first_entry.keys() 
                               if key in ["lean", "dafny", "verus"] and first_entry[key])
        
        # Check that all other entries have the same signature
        for filename, entry_data in source_entries.items():
            entry_signature = set(key for key in entry_data.keys() 
                                if key in ["lean", "dafny", "verus"] and entry_data[key])
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

def print_summary_counts(source_meta: Dict[str, Any]) -> None:
    """Print total counts of files by source and language type."""


    not_novel = [('dafny', 'dafnybench'), ('dafny', 'humaneval'),
                 ('verus', 'verified_cogen'), ('lean', 'verina'),
                 ('lean', 'fvapps'), ('lean', 'clever')]

    # Initialize totals
    total = {}
    for novelty in ['all', 'novel']:
        total[novelty] = {}
        for lang in ['lean', 'dafny', 'verus']:
            total[novelty][lang] = {}
            for file_type in ['yaml', 'poor']:
                total[novelty][lang][file_type] = 0
    
    # Count files by source and language type
    source_counts = count_files_by_source(source_meta)
       
    # Print counts for each source and accumulate totals
    print("\nFile counts by source:")
    print("=" * 50)
    for source, counts in sorted(source_counts.items()):
        print(f"Source: {source}")
        print(f"  Total files: {counts['total']}")
        print(f"  Lean files: {counts['lean']['yaml']+counts['lean']['poor']} : {counts['lean']['yaml']} ")
        print(f"  Dafny files: {counts['dafny']['yaml']+counts['dafny']['poor']} : {counts['dafny']['yaml']} ")
        print(f"  Verus files: {counts['verus']['yaml']+counts['verus']['poor']} : {counts['verus']['yaml']} ")
        print()
        
        # Accumulate totals
        for lang in ['lean', 'dafny', 'verus']:
            for file_type in ['yaml', 'poor']:
                total['all'][lang][file_type] += counts[lang][file_type]
                total['novel'][lang][file_type] += counts[lang][file_type] * (0 if (lang, source) in not_novel else 1)
    
    # Print grand totals
    print("=" * 50)
    print("GRAND TOTALS")
    print("=" * 50)
    print(f"Lean total (all): {total['all']['lean']['yaml'] + total['all']['lean']['poor']} : {total['all']['lean']['yaml']}")
    print(f"Lean total (novel): {total['novel']['lean']['yaml'] + total['novel']['lean']['poor']} : {total['novel']['lean']['yaml']}")
    print(f"Dafny total (all): {total['all']['dafny']['yaml'] + total['all']['dafny']['poor']} : {total['all']['dafny']['yaml']}")
    print(f"Dafny total (novel): {total['novel']['dafny']['yaml'] + total['novel']['dafny']['poor']} : {total['novel']['dafny']['yaml']}")
    print(f"Verus total (all): {total['all']['verus']['yaml'] + total['all']['verus']['poor']} : {total['all']['verus']['yaml']}")
    print(f"Verus total (novel): {total['novel']['verus']['yaml'] + total['novel']['verus']['poor']} : {total['novel']['verus']['yaml']}")
    print("=" * 50)

    # Print grand totals
    grand_total = {}
    for novelty in ['all', 'novel']:
        grand_total[novelty] = {}
        for file_type in ['yaml', 'poor']:
            grand_total[novelty][file_type] = 0
            for lang in ['lean', 'dafny', 'verus']:
                grand_total[novelty][file_type] += total[novelty][lang][file_type]

    print(f"Grand total (all):  {grand_total['all']['yaml'] + grand_total['all']['poor']} : {grand_total['all']['yaml']}")  
    print(f"Grand total (novel): {grand_total['novel']['yaml'] + grand_total['novel']['poor']} : {grand_total['novel']['yaml']}")
    print("=" * 50)

def generate_ids(source_meta: Dict[str, Any]) -> None:
    """Generate IDs for the files in source_meta.
    
    For each source, sorts all files and assigns them four-digit zero-padded IDs
    starting from 0000.
    """
    # Group files by source
    files_by_source = {}
    for filename, file_data in source_meta.items():
        source = file_data.get("source")
        if source is None:
            raise ValueError(f"Source is None for {filename}")
        if source not in files_by_source:
            files_by_source[source] = []
        files_by_source[source].append(filename)
    
    # Sort files within each source and assign IDs
    for source, filenames in files_by_source.items():
        # Sort filenames alphabetically
        sorted_filenames = sorted(filenames)
        
        # Assign four-digit zero-padded IDs starting from 0000
        for i, filename in enumerate(sorted_filenames):
            file_id = f"{i:04d}"  # Four-digit zero-padded string
            source_meta[filename]["id"] = file_id
    
    return source_meta


def main():
    """Main function to extract metadata from benchmarks directory."""
    benchmarks_dir = Path("benchmarks")
    
    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")
    
    # Get source metadata
    source_meta = get_source_meta(benchmarks_dir, save_path=benchmarks_dir / "generated_metadata.json")

    # Validate that all entries for each source have consistent signatures
    # validate_source_signatures(source_meta)
    
    # Print summary counts
    print_summary_counts(source_meta)


if __name__ == "__main__":
    main()
