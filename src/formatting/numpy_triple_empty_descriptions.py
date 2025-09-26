#!/usr/bin/env python3
"""
Script to find all YAML files in the numpy_yaml directory where the vc-description field is empty.
"""

import os
import yaml
from pathlib import Path


def is_description_empty(file_path):
    """
    Check if the vc-description field in a YAML file is empty.

    Args:
        file_path (str): Path to the YAML file

    Returns:
        bool: True if vc-description is empty, False otherwise
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()

        # Parse YAML content
        data = yaml.safe_load(content)

        # Check if vc-description exists and is empty
        if "vc-description" in data:
            description = data["vc-description"]
            # Check if description is None, empty string, or contains only whitespace
            if description is None or (
                isinstance(description, str) and description.strip() == ""
            ):
                return True
        return False

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return False


def find_empty_descriptions(directory):
    """
    Find all YAML files in the specified directory where vc-description is empty.

    Args:
        directory (str): Directory path to search

    Returns:
        list: List of file paths with empty descriptions
    """
    empty_files = []

    # Get all YAML files in the directory
    yaml_files = list(Path(directory).glob("*.yaml"))

    print(f"Scanning {len(yaml_files)} YAML files in {directory}...")

    for yaml_file in yaml_files:
        if is_description_empty(yaml_file):
            empty_files.append(str(yaml_file))

    return empty_files


def main():
    """Main function to find and display files with empty descriptions."""
    # Directory to search
    numpy_yaml_dir = "benchmarks/lean/numpy_yaml"

    # Check if directory exists
    if not os.path.exists(numpy_yaml_dir):
        print(f"Directory {numpy_yaml_dir} does not exist!")
        return

    # Find files with empty descriptions
    empty_files = find_empty_descriptions(numpy_yaml_dir)

    # Display results
    print(f"\nFound {len(empty_files)} files with empty vc-description:")
    print("=" * 60)

    if empty_files:
        for file_path in sorted(empty_files):
            # Extract just the filename for cleaner output
            filename = os.path.basename(file_path)
            print(f"  {filename}")

        print(f"\nTotal: {len(empty_files)} files need descriptions")
    else:
        print("  No files found with empty descriptions!")


if __name__ == "__main__":
    main()
