#!/usr/bin/env python3

import argparse
import yaml
from pathlib import Path


def convert_yaml_to_file(yaml_path: Path, suffix: str) -> None:
    """Convert YAML spec to target file format by concatenating sections."""
    
    with open(yaml_path, 'r') as f:
        spec = yaml.safe_load(f)
    
    parts = []
    
    # Add sections in order, following the reconstruction logic
    for section in ['vc-preamble', 'vc-helpers', 'vc-spec', 'vc-code', 'vc-postamble']:
        if section in spec and spec[section]:
            parts.append(spec[section])
    
    # Join with newlines, filtering out empty parts
    content = '\n\n'.join(part.strip() for part in parts if part.strip())
    
    # Generate output filename
    output_path = yaml_path.with_suffix(f'.{suffix}')
    
    with open(output_path, 'w') as f:
        f.write(content)
    
    print(f"Converted {yaml_path} -> {output_path}")


def main():
    parser = argparse.ArgumentParser(description='Convert YAML spec to target file format')
    parser.add_argument('yaml_file', type=Path, help='Input YAML file')
    parser.add_argument('--suffix', required=True, choices=['dfy', 'lean', 'rs'], 
                       help='Output file suffix')
    
    args = parser.parse_args()
    
    if not args.yaml_file.exists():
        print(f"Error: {args.yaml_file} does not exist")
        return 1
    
    convert_yaml_to_file(args.yaml_file, args.suffix)
    return 0


if __name__ == '__main__':
    exit(main())