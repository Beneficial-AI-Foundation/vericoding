#!/usr/bin/env python3
"""
Script to check compilation of Lean files and organize YAML files based on compilation status.

This script:
1. Iterates through .lean files in benchmarks/lean/apps_train/files/ that have corresponding YAML files
2. Runs `lake build` on each file to check if it compiles
3. If a file compiles successfully, moves the corresponding YAML file to compiling folder
4. If a file doesn't compile, moves the corresponding YAML file to non_compiling folder
"""

import os
import subprocess
import shutil
from pathlib import Path
from typing import List, Tuple


def get_lean_files_with_yaml(files_dir: Path, yaml_dir: Path) -> List[Path]:
    """Get all .lean files from the files directory that have a corresponding YAML file."""
    lean_files = []
    for lean_file in files_dir.glob("*.lean"):
        sample_id = extract_sample_id(lean_file)
        yaml_file = yaml_dir / f"sample_{sample_id}.yaml"
        if yaml_file.exists():
            lean_files.append(lean_file)
        else:
            print(f"Skipping {lean_file.name} - no corresponding YAML file found")
    return lean_files


def extract_sample_id(lean_file: Path) -> str:
    """Extract sample ID from filename like 'sample_004709.lean' -> '004709'."""
    filename = lean_file.stem  # Remove .lean extension
    if filename.startswith("sample_"):
        return filename[7:]  # Remove "sample_" prefix
    raise ValueError(f"Unexpected filename format: {lean_file.name}")


def check_lean_compilation(lean_file: Path, project_root: Path) -> bool:
    """
    Check if a Lean file compiles by running `lake build` on it.
    
    Args:
        lean_file: Path to the .lean file
        project_root: Root directory of the Lean project
        
    Returns:
        True if compilation succeeds, False otherwise
    """
    # Convert to relative path from project root
    relative_path = lean_file.relative_to(project_root)
    
    try:
        # Run lake build on the specific file
        result = subprocess.run(
            ["lake", "build", str(relative_path)],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=60  # 60 second timeout
        )
        
        # Return True if exit code is 0 (success)
        return result.returncode == 0
        
    except subprocess.TimeoutExpired:
        print(f"Timeout compiling {lean_file.name}")
        return False
    except Exception as e:
        print(f"Error compiling {lean_file.name}: {e}")
        return False


def move_yaml_file(sample_id: str, yaml_dir: Path, target_dir: Path, folder_name: str) -> bool:
    """
    Move the corresponding YAML file to the specified directory.
    
    Args:
        sample_id: The sample ID (e.g., "004709")
        yaml_dir: Directory containing YAML files
        target_dir: Directory to move YAML files to
        folder_name: Name of the folder for logging purposes
        
    Returns:
        True if file was moved successfully, False otherwise
    """
    yaml_file = yaml_dir / f"sample_{sample_id}.yaml"
    target_file = target_dir / f"sample_{sample_id}.yaml"
    
    if not yaml_file.exists():
        print(f"Warning: YAML file {yaml_file.name} not found")
        return False
    
    try:
        # Ensure target directory exists
        target_dir.mkdir(parents=True, exist_ok=True)
        
        # Move the file
        shutil.move(str(yaml_file), str(target_file))
        print(f"Moved {yaml_file.name} to {folder_name} folder")
        return True
        
    except Exception as e:
        print(f"Error moving {yaml_file.name}: {e}")
        return False


def main():
    """Main function to process all Lean files."""
    # Define paths
    script_dir = Path(__file__).parent
    project_root = script_dir.parent.parent  # Go up to vericoding root
    files_dir = project_root / "benchmarks" / "lean" / "apps_train" / "files"
    yaml_dir = project_root / "benchmarks" / "lean" / "apps_train" / "yaml"
    compiling_dir = project_root / "benchmarks" / "lean" / "apps_train" / "compiling"
    non_compiling_dir = project_root / "benchmarks" / "lean" / "apps_train" / "non_compiling"
    
    print(f"Project root: {project_root}")
    print(f"Files directory: {files_dir}")
    print(f"YAML directory: {yaml_dir}")
    print(f"Compiling directory: {compiling_dir}")
    print(f"Non-compiling directory: {non_compiling_dir}")
    
    # Verify directories exist
    if not files_dir.exists():
        print(f"Error: Files directory {files_dir} does not exist")
        return 1
    
    if not yaml_dir.exists():
        print(f"Error: YAML directory {yaml_dir} does not exist")
        return 1
    
    # Get all Lean files that have corresponding YAML files
    lean_files = get_lean_files_with_yaml(files_dir, yaml_dir)
    print(f"Found {len(lean_files)} Lean files with corresponding YAML files to check")
    
    if not lean_files:
        print("No Lean files with corresponding YAML files found")
        return 0
    
    # Statistics
    total_files = len(lean_files)
    compiling_files = 0
    non_compiling_files = 0
    moved_to_compiling = 0
    moved_to_non_compiling = 0
    
    # Process each file
    for i, lean_file in enumerate(lean_files, 1):
        print(f"\n[{i}/{total_files}] Checking {lean_file.name}...")
        
        try:
            sample_id = extract_sample_id(lean_file)
        except ValueError as e:
            print(f"Error: {e}")
            continue
        
        # Check compilation
        if check_lean_compilation(lean_file, project_root):
            print(f"✓ {lean_file.name} compiles successfully")
            compiling_files += 1
            
            # Move corresponding YAML file to compiling folder
            if move_yaml_file(sample_id, yaml_dir, compiling_dir, "compiling"):
                moved_to_compiling += 1
        else:
            print(f"✗ {lean_file.name} failed to compile")
            non_compiling_files += 1
            
            # Move corresponding YAML file to non_compiling folder
            if move_yaml_file(sample_id, yaml_dir, non_compiling_dir, "non_compiling"):
                moved_to_non_compiling += 1
    
    # Print summary
    print(f"\n{'='*50}")
    print("SUMMARY")
    print(f"{'='*50}")
    print(f"Total files processed: {total_files}")
    print(f"Compiling files: {compiling_files}")
    print(f"Non-compiling files: {non_compiling_files}")
    print(f"YAML files moved to compiling: {moved_to_compiling}")
    print(f"YAML files moved to non_compiling: {moved_to_non_compiling}")
    
    if compiling_files > 0:
        print(f"\nCompiling YAML files moved to: {compiling_dir}")
    if non_compiling_files > 0:
        print(f"Non-compiling YAML files moved to: {non_compiling_dir}")
    
    return 0


if __name__ == "__main__":
    exit(main())
