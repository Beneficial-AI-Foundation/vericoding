#!/usr/bin/env python3
"""
Convert YAML files to Dafny spec files using yaml_to_code with spec=True and vibe=True.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Add src to path to import our modules
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from vericoding.processing.yaml_processor import load_yaml, yaml_to_code

SOURCE_DIR = ROOT / "benchmarks" / "dafny" / "humaneval" / "yaml"
TARGET_DIR = ROOT / "benchmarks" / "dafny" / "humaneval" / "spec"


def convert_yaml_to_spec(yaml_path: Path, output_dir: Path) -> bool:
    """Convert a single YAML file to a Dafny spec file."""
    try:
        # Load YAML data
        data = load_yaml(yaml_path)
        
        # Convert to Dafny code with both spec and vibe
        dafny_code = yaml_to_code(data, spec=True, vibe=True)
        
        # Create output file path
        output_path = output_dir / (yaml_path.stem + ".dfy")
        
        # Write the Dafny code
        output_path.write_text(dafny_code, encoding="utf-8")
        return True
    except Exception as e:
        print(f"Error converting {yaml_path.name}: {e}")
        return False


def main() -> None:
    if not SOURCE_DIR.exists():
        print(f"Source directory not found: {SOURCE_DIR}")
        return
    
    # Create target directory
    TARGET_DIR.mkdir(parents=True, exist_ok=True)
    
    # Find all YAML files
    yaml_files = list(SOURCE_DIR.glob("*.yaml"))
    if not yaml_files:
        print(f"No YAML files found in {SOURCE_DIR}")
        return
    
    print(f"Converting {len(yaml_files)} YAML files...")
    
    converted = 0
    for yaml_file in sorted(yaml_files):
        if convert_yaml_to_spec(yaml_file, TARGET_DIR):
            converted += 1
    
    print(f"Successfully converted {converted} files to {TARGET_DIR}")


if __name__ == "__main__":
    main()
