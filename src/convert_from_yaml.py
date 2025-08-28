#!/usr/bin/env python3

import argparse
import json
from pathlib import Path
from ruamel.yaml import YAML

def spec_to_string(spec: dict, template: list[str]) -> str:
    """Convert YAML spec dict to string by concatenating sections."""
    parts = []
    
    # Add sections in order, following the reconstruction logic
    for section in template:
        if section == '\n': # empty line
            # if tail of parts is non-empty, add an empty line
            if parts and parts[-1].strip():
                parts.append('')
        elif section in spec:
            if spec[section].rstrip(): # non-empty line
                parts.append(spec[section].rstrip())
        else: # section not in spec
            print(f"Warning: Section {section} not found in spec")
    
    # Join with newlines
    return '\n'.join(parts)

def get_template(suffix: str) -> list[str]:
    """Get template for the output file."""
    if suffix == 'lean':
        return ['vc-preamble', '\n', 'vc-description', '\n', 'vc-helpers', '\n', 
                    'vc-signature', 'vc-implementation', '\n', 
                    'vc-condition', 'vc-proof', '\n', 'vc-postamble']
    elif suffix == 'dfy' or suffix == 'rs':
        return ['vc-description', '\n', 'vc-preamble', '\n', 'vc-helpers', '\n', 
                    'vc-spec', 'vc-code', '\n', 'vc-postamble']
    else:
        raise ValueError(f"Unsupported suffix: {suffix}")

def convert_yaml_to_file(yaml_path: Path, output_path: Path) -> None:
    """Convert YAML spec to target file format by concatenating sections."""
    
    yaml = YAML(typ='safe')
    spec = yaml.load(yaml_path)
    
    template = get_template(output_path.suffix[1:])
    
    content = spec_to_string(spec, template)
    
    with open(output_path, 'w') as f:
        f.write(content)
    
    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_json(yaml_path: Path, output_path: Path) -> None:
    """Convert YAML spec to a JSON file."""

    yaml = YAML(typ='safe')
    spec = yaml.load(yaml_path)

    with open(output_path, 'w') as f:
        json.dump(spec, f, ensure_ascii=False, indent=2)

    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_jsonl(yaml_path: Path) -> None:
    """Convert all YAML files in a directory to a single JSONL file."""
    
    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")
    
    # Find all .yaml files in the directory
    yaml_files = list(yaml_path.glob("*.yaml"))
    
    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return
    
    # Create output path in parent directory with .jsonl suffix
    output_path = yaml_path.parent / f"{yaml_path.name}.jsonl"
    
    with open(output_path, 'w') as f:
        yaml = YAML(typ='safe')
        for yaml_file in yaml_files:
            # Load the YAML spec
            spec = yaml.load(yaml_file)
            
            # Add the id field (filename without .yaml suffix)
            spec['id'] = yaml_file.stem
            
            # Write as JSON line
            json.dump(spec, f, ensure_ascii=False)
            f.write('\n')
    
    print(f"Converted {len(yaml_files)} YAML files to {output_path}")


def convert_yaml_to_dir(yaml_path: Path, suffix: str) -> None:
    """Convert all YAML files in a directory to a new directory with specified suffix."""
    
    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")
    
    # Find all .yaml files in the directory
    yaml_files = list(yaml_path.glob("*.yaml"))
    
    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return
    
    # Create output directory path
    output_dir = yaml_path.parent / f"{yaml_path.name}_{suffix}"
    
    # Create the output directory if it doesn't exist
    output_dir.mkdir(exist_ok=True)
    
    if suffix in ['lean', 'dfy', 'rs']:
        for yaml_file in yaml_files:
            output_file = output_dir / f"{yaml_file.stem}.{suffix}"
            convert_yaml_to_file(yaml_file, output_file)  

    elif suffix == 'json':
        for yaml_file in yaml_files:
            output_file = output_dir / f"{yaml_file.stem}.{suffix}"
            convert_yaml_to_json(yaml_file, output_file)

    else:
        raise ValueError(f"Unsupported suffix: {suffix}")
    
    print(f"Converted {len(yaml_files)} YAML files to {output_dir}")


def main():
    parser = argparse.ArgumentParser(description='Convert YAML spec to target file format')
    parser.add_argument('yaml_file', type=Path, help='Input YAML file or directory')
    parser.add_argument('--suffix', required=True, choices=['dfy', 'lean', 'rs', 'json', 'jsonl'], 
                       help='Output file suffix')
    parser.add_argument('--dir', action='store_true', 
                       help='Convert all YAML files in directory to a new directory (not available for jsonl)')
    
    args = parser.parse_args()
    
    if not args.yaml_file.exists():
        raise FileNotFoundError(f"{args.yaml_file} does not exist")
    
    if args.dir:
        if args.suffix == 'jsonl':
            print("Error: --dir option is not available for jsonl suffix (use without --dir for JSONL)")
            return
        convert_yaml_to_dir(args.yaml_file, args.suffix)
    elif args.suffix == 'json':
        output_path = args.yaml_file.with_suffix(f'.{args.suffix}')
        convert_yaml_to_json(args.yaml_file, output_path)
    elif args.suffix == 'jsonl':
        convert_yaml_to_jsonl(args.yaml_file)
    else:
        output_path = args.yaml_file.with_suffix(f'.{args.suffix}')
        convert_yaml_to_file(args.yaml_file, output_path)


if __name__ == '__main__':
    main()
