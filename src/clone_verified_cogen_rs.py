#!/usr/bin/env python3
"""
Script to clone verified-cogen repository and extract Rust files from benches directory.
"""

import json
import tempfile
import uuid
from dataclasses import dataclass
from pathlib import Path
from typing import List, Dict, Any
import os

import git
from dataclasses_json import dataclass_json


@dataclass_json
@dataclass
class RustFile:
    """Data class to hold Rust file content and path."""
    content: str
    path: str


def clone_repo(repo_url: str, temp_dir: Path) -> Path:
    """Clone the repository to a temporary directory."""
    print(f"Cloning {repo_url} to {temp_dir}")
    git.Repo.clone_from(repo_url, temp_dir)
    return temp_dir


def find_rust_files(benches_dir: Path) -> List[Path]:
    """Recursively find all .rs files in the benches directory."""
    if not benches_dir.exists():
        raise FileNotFoundError(f"Benches directory not found: {benches_dir}")
    
    rust_files = list(benches_dir.rglob("*.rs"))
    print(f"Found {len(rust_files)} .rs files in {benches_dir}")
    return rust_files


def read_rust_files(rust_files: List[Path], base_path: Path) -> List[RustFile]:
    """Read content of all Rust files and create RustFile objects."""
    rust_file_objects = []
    
    for file_path in rust_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Create relative path from verified-cogen/benches/...
            relative_path = file_path.relative_to(base_path)
            path_str = f"verified-cogen/{relative_path}"
            
            rust_file_objects.append(RustFile(content=content, path=path_str))
            
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            continue
    
    return rust_file_objects


def filter_duplicates(rust_files: List[RustFile]) -> List[RustFile]:
    """Filter out duplicates based on basename (filename without directory)."""
    seen_basenames = set()
    filtered_files = []
    
    for rust_file in rust_files:
        basename = Path(rust_file.path).name
        
        if basename not in seen_basenames:
            seen_basenames.add(basename)
            filtered_files.append(rust_file)
        else:
            print(f"Filtering out duplicate: {rust_file.path} (basename: {basename})")
    
    print(f"Filtered {len(rust_files)} files down to {len(filtered_files)} unique files")
    return filtered_files


def write_json_output(rust_files: List[RustFile], output_file: Path) -> None:
    """Write the list of RustFile objects to JSON."""
    # Convert to dictionaries for JSON serialization
    data = [rust_file.to_dict() for rust_file in rust_files]
    
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    
    print(f"Written {len(rust_files)} files to {output_file}")


def main():
    """Main function to orchestrate the cloning and extraction process."""
    repo_url = "https://github.com/JetBrains-Research/verified-cogen"
    
    # Create temporary directory with UUID
    temp_dir_name = f"verified-cogen-{uuid.uuid4()}"
    temp_dir = Path(tempfile.gettempdir()) / temp_dir_name
    
    try:
        # Clone repository
        repo_path = clone_repo(repo_url, temp_dir)
        
        # Find benches directory
        benches_dir = repo_path / "benches"
        
        # Find all .rs files
        rust_files = find_rust_files(benches_dir)
        
        # Read file contents
        rust_file_objects = read_rust_files(rust_files, repo_path)
        
        # Filter duplicates
        unique_rust_files = filter_duplicates(rust_file_objects)
        
        # Write JSON output to the same temp directory as the clone
        output_file = temp_dir / "rust_files_from_verified_cogen.json"
        write_json_output(unique_rust_files, output_file)
        
        print(f"Successfully extracted and filtered {len(unique_rust_files)} unique Rust files")
        print(f"Files saved to: {output_file}")
        print(f"Temporary directory preserved at: {temp_dir}")
        
    except Exception as e:
        print(f"Error: {e}")
        # Don't clean up on error so you can inspect what went wrong


if __name__ == "__main__":
    main()