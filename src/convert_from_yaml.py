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
    result = '\n'.join(parts)
    # Ensure final newline if content exists
    if result and not result.endswith('\n'):
        result += '\n'
    return result

def get_template(suffix: str) -> list[str]:
    """Get template for the output file."""
    if suffix == 'lean':
        return ['vc-description', '\n', 'vc-preamble', '\n', 'vc-helpers', '\n', 
                    'vc-signature', 'vc-implementation', '\n', 
                    'vc-condition', 'vc-proof', '\n', 'vc-postamble']
    elif suffix == 'dfy' or suffix == 'rs':
        return ['vc-description', '\n', 'vc-preamble', '\n', 'vc-helpers', '\n', 
                    'vc-spec', 'vc-code', '\n', 'vc-postamble']
    else:
        raise ValueError(f"Unsupported suffix: {suffix}")

def convert_spec_to_file(spec: dict, output_path: Path) -> None:
    """Convert spec dictionary to target file format by concatenating sections."""
    
    template = get_template(output_path.suffix[1:])
    
    content = spec_to_string(spec, template)
    
    with open(output_path, 'w') as f:
        f.write(content)
    
    # print(f"Converted spec -> {output_path}")


def convert_yaml_to_file(yaml_path: Path, output_path: Path) -> None:
    """Convert YAML spec to target file format by concatenating sections."""
    
    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting
    spec = yaml.load(yaml_path)
    
    convert_spec_to_file(spec, output_path)
    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_json(yaml_path: Path, output_path: Path) -> None:
    """Convert YAML spec to a JSON file."""

    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting
    spec = yaml.load(yaml_path)

    with open(output_path, 'w') as f:
        json.dump(spec, f, ensure_ascii=False, indent=2)

    print(f"Converted {yaml_path} -> {output_path}")


def convert_yaml_to_jsonl(yaml_path: Path, output_path: Path = None) -> None:
    """Convert all YAML files in a directory to a single JSONL file."""
    
    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")
    
    # Find all .yaml files in the directory
    yaml_files = list(yaml_path.glob("*.yaml"))
    
    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return
    
    # Create output path in parent directory with .jsonl suffix
    if output_path is None:
        output_path = yaml_path.parent / f"{yaml_path.name}.jsonl"
    
    with open(output_path, 'w') as f:
        yaml = YAML()
        yaml.preserve_quotes = True  # Preserve original formatting
        for yaml_file in yaml_files:
            # Load the YAML spec
            spec = yaml.load(yaml_file)
            
            # Create a new dictionary with id field first
            new_spec = {'id': yaml_file.stem}
            new_spec.update(spec)
            
            # Write as JSON line
            json.dump(new_spec, f, ensure_ascii=False)
            f.write('\n')
    
    print(f"Converted {len(yaml_files)} YAML files to {output_path}")


def convert_yaml_to_dir(suffix: str, yaml_path: Path, output_path: Path = None) -> None:
    """Convert all YAML files in a directory to a new directory with specified suffix."""
    
    if not yaml_path.is_dir():
        raise ValueError(f"{yaml_path} is not a directory")
    
    # Find all .yaml files in the directory
    yaml_files = list(yaml_path.glob("*.yaml"))
    
    if not yaml_files:
        print(f"No .yaml files found in {yaml_path}")
        return
    
    # Create output directory path
    if output_path is None:
        output_dir = yaml_path.parent / f"{yaml_path.name}_{suffix}"
    else:
        output_dir = output_path
    
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


def convert_jsonl_to_dir(suffix: str, jsonl_path: Path, output_path: Path = None) -> None:
    """Convert all entries in a JSONL file to individual files with specified suffix."""
    
    if not jsonl_path.is_file():
        raise ValueError(f"{jsonl_path} is not a file")
    
    # Create output directory path
    if output_path is None:
        output_dir = jsonl_path.parent / f"{jsonl_path.stem}_{suffix}"
    else:
        output_dir = output_path
    
    # Create the output directory if it doesn't exist
    output_dir.mkdir(exist_ok=True)
    
    # Read JSONL file and process each line
    processed_count = 0
    with open(jsonl_path, 'r') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:  # Skip empty lines
                continue
            
            try:
                # Parse JSON line
                spec = json.loads(line)
                
                # Check if id field exists
                if 'id' not in spec:
                    print(f"Warning: Line {line_num} missing 'id' field, skipping")
                    continue
                
                file_id = spec['id']
                
                if suffix in ['lean', 'dfy', 'rs']:
                    output_file = output_dir / f"{file_id}.{suffix}"
                    convert_spec_to_file(spec, output_file)
                
                elif suffix == 'json':
                    output_file = output_dir / f"{file_id}.{suffix}"
                    with open(output_file, 'w') as out_f:
                        json.dump(spec, out_f, ensure_ascii=False, indent=2)
                
                else:
                    raise ValueError(f"Unsupported suffix: {suffix}")
                
                processed_count += 1
                
            except json.JSONDecodeError as e:
                print(f"Warning: Invalid JSON on line {line_num}: {e}")
                continue
    
    if processed_count == 0:
        print(f"No valid entries found in {jsonl_path}")
    else:
        print(f"Converted {processed_count} entries from {jsonl_path} to {output_dir}")


def process_benchmarks(benchmarks_dir: Path, suffix: str = None) -> None:
    """Process benchmark directories to convert YAML files.
    
    For each level-2 subfolder of benchmarks/XXX/YYY:
    1. Look for a 'yaml' folder
    2. If it exists, convert YAML files to files with the appropriate suffix in 'files' folder
       (suffix determined by XXX: dafny->dfy, lean->lean, verus->rs)
    3. Convert all YAML files to a JSONL file using custom naming: XXX_YYY.jsonl
    """
    
    if not benchmarks_dir.exists():
        raise FileNotFoundError(f"Benchmarks directory {benchmarks_dir} does not exist")
    
    if not benchmarks_dir.is_dir():
        raise ValueError(f"{benchmarks_dir} is not a directory")
    
    # Find all level-2 subdirectories (benchmarks/XXX/YYY)
    level2_dirs = []
    for level1_dir in benchmarks_dir.iterdir():
        if level1_dir.is_dir():
            for level2_dir in level1_dir.iterdir():
                if level2_dir.is_dir():
                    level2_dirs.append(level2_dir)
    
    if not level2_dirs:
        print(f"No level-2 subdirectories found in {benchmarks_dir}")
        return
    
    processed_count = 0
    
    for level2_dir in level2_dirs:
        yaml_dir = level2_dir / "yaml"
        
        # Check if yaml folder exists
        if not yaml_dir.exists() or not yaml_dir.is_dir():
            continue
        
        # Determine suffix based on level-1 directory name (XXX)
        level1_name = level2_dir.parent.name
        if suffix is None:
            if level1_name == "dafny":
                dir_suffix = "dfy"
            elif level1_name == "lean":
                dir_suffix = "lean"
            elif level1_name == "verus":
                dir_suffix = "rs"
            else:
                raise ValueError(f"Unknown benchmark type '{level1_name}'. Expected 'dafny', 'lean', or 'verus'")
        else:
            dir_suffix = suffix
        
        print(f"Processing {level2_dir} with suffix '{dir_suffix}'...")
        
        # 1. Convert all YAML files to JSONL using custom naming: XXX_YYY.jsonl
        level2_name = level2_dir.name
        jsonl_filename = f"{level1_name}_{level2_name}.jsonl"
        jsonl_path = level2_dir / jsonl_filename
        convert_yaml_to_jsonl(yaml_dir, jsonl_path)
        
        # 2. Convert JSONL to individual files in 'files' folder
        files_dir = level2_dir / "files"
        convert_jsonl_to_dir(dir_suffix, jsonl_path, files_dir)
        
        processed_count += 1
    
    print(f"Processed {processed_count} benchmark directories")


def spec_to_yaml(spec: dict, yaml_path: Path, required_keys: list[str] = None) -> None:
    """Write a spec dictionary to a YAML file with proper multiline string formatting.
    
    Args:
        spec: Dictionary containing the spec data
        yaml_path: Path to the output YAML file
        required_keys: List of keys that must be present in spec, in the order they should appear in the YAML file.
                      If None, writes all keys in arbitrary order without validation.
    """
    
    # Validate required keys if provided
    if required_keys is not None:
        # Check for missing required keys
        missing_keys = [key for key in required_keys if key not in spec]
        if missing_keys:
            raise ValueError(f"Missing required keys in spec: {missing_keys}")
        
        # Check for extra keys not in required list
        extra_keys = [key for key in spec.keys() if key not in required_keys]
        if extra_keys:
            raise ValueError(f"Spec contains keys not in required list: {extra_keys}")
        
        # Use required_keys for ordering
        keys_to_write = required_keys
    else:
        # Use all keys in arbitrary order
        keys_to_write = list(spec.keys())
    
    # Manually write the YAML file with multiline strings
    with open(yaml_path, 'w') as f:
        for key in keys_to_write:
            value = spec[key]
            # Write the key with multiline indicator
            f.write(f"{key}: |-\n")
            
            # Write the value in multiline format
            if isinstance(value, str):
                stripped_value = value.rstrip()
                if stripped_value:
                    # Split into lines and add two spaces to each line
                    lines = stripped_value.split('\n')
                    for line in lines:
                        f.write('  ' + line + '\n')
                    f.write('\n')
                else:
                    f.write('\n')
            else:
                raise ValueError(f"Unsupported value type: {type(value)}")


def clear_implementation(yaml_path: Path) -> None:
    """Read a YAML file, replace vc-implementation, vc-proof, and vc-code fields with empty strings, and write back."""
    
    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting
    
    # Load the YAML file
    with open(yaml_path, 'r') as f:
        spec = yaml.load(f)
    
    # Replace the specified fields with empty strings
    fields_to_clear = ['vc-implementation', 'vc-proof']
    for field in fields_to_clear:
        if field in spec:
            spec[field] = "-- <"+field+">\n  sorry\n-- </"+field+">\n\n"
    
    # Write the modified spec back to YAML
    # Get required keys in the order they appeared in the original file 
    # Thankfully ruamel.yaml preserves the order of keys when loading
    required_keys = [key for key in spec.keys()]
    spec_to_yaml(spec, yaml_path, required_keys=required_keys)
    
    print(f"Cleared implementation fields in {yaml_path}")


def main():
    parser = argparse.ArgumentParser(description='Convert YAML spec to target file format')
    parser.add_argument('yaml_file', type=Path, nargs='?', help='Input YAML file or directory')
    parser.add_argument('--suffix', choices=['dfy', 'lean', 'rs', 'json', 'jsonl'], 
                       help='Output file suffix')
    parser.add_argument('--dir', action='store_true', 
                       help='Convert all YAML files in directory to a new directory (not available for jsonl)')
    parser.add_argument('--clear-impl', action='store_true',
                       help='Clear vc-implementation, vc-proof, and vc-code fields with empty strings')
    parser.add_argument('--benchmarks', type=Path, metavar='BENCHMARKS_DIR',
                       help='Process benchmark directories. For each level-2 subfolder benchmarks/XXX/YYY, '
                            'convert YAML files in yaml/ folder to files/ folder and create JSONL file')
    
    args = parser.parse_args()
    
    # Handle benchmarks processing
    if args.benchmarks is not None:
        process_benchmarks(args.benchmarks, args.suffix)
        return
    
    # For non-benchmarks processing, yaml_file is required
    if args.yaml_file is None:
        parser.error("yaml_file is required when not using --benchmarks")
    
    if not args.yaml_file.exists():
        raise FileNotFoundError(f"{args.yaml_file} does not exist")
    
    # Handle clear implementation fields option
    if args.clear_impl:
        if args.yaml_file.is_file():
            clear_implementation(args.yaml_file)
        elif args.yaml_file.is_dir():
            # Process all YAML files in directory
            yaml_files = list(args.yaml_file.glob("*.yaml"))
            if not yaml_files:
                print(f"No .yaml files found in {args.yaml_file}")
                return
            for yaml_file in yaml_files:
                clear_implementation(yaml_file)
            print(f"Cleared implementation fields in {len(yaml_files)} YAML files")
        return
    
    # Original conversion logic
    if not args.suffix:
        parser.error("--suffix is required when not using --clear-impl")
    
    if args.dir:
        if args.suffix == 'jsonl':
            print("Error: --dir option is not available for jsonl suffix (use without --dir for JSONL)")
            return
        convert_yaml_to_dir(args.suffix, args.yaml_file)
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
