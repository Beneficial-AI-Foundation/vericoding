#!/usr/bin/env python3
"""
Remove /-- and -/ comment markers from vc-description sections in YAML files.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
YAML_DIR = ROOT / "benchmarks" / "dafny" / "humaneval" / "yaml"


def clean_file(path: Path) -> bool:
    """Remove /-- and -/ markers from vc-description in a YAML file."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
        modified = False
        
        in_desc = False
        new_lines = []
        
        for line in lines:
            if line.startswith("vc-description: |-"):
                in_desc = True
                new_lines.append(line)
                continue
            
            if in_desc:
                # Check if we've reached the next section
                if line and not line.startswith("  ") and not line == "":
                    in_desc = False
                    new_lines.append(line)
                    continue
                
                # Remove /-- and -/ markers
                stripped = line.strip()
                if stripped == "/--" or stripped == "-/":
                    modified = True
                    continue  # Skip this line
                
                new_lines.append(line)
            else:
                new_lines.append(line)
        
        if modified:
            path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")
            return True
        return False
    except Exception as e:
        print(f"Error processing {path.name}: {e}")
        return False


def main() -> None:
    if not YAML_DIR.exists():
        print(f"YAML directory not found: {YAML_DIR}")
        return
    
    yaml_files = list(YAML_DIR.glob("*.yaml"))
    if not yaml_files:
        print(f"No YAML files found in {YAML_DIR}")
        return
    
    print(f"Cleaning vc-description comments in {len(yaml_files)} YAML files...")
    
    modified = 0
    for yaml_file in sorted(yaml_files):
        if clean_file(yaml_file):
            modified += 1
    
    print(f"Modified {modified} files")


if __name__ == "__main__":
    main()
