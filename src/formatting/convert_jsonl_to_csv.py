#!/usr/bin/env python3
"""
JSONL to CSV Converter

This script converts JSON Lines (JSONL) files to CSV format.
It automatically detects all fields across all records and creates a comprehensive CSV.

Usage:
    python convert_jsonl_to_csv.py input.jsonl output.csv
    python convert_jsonl_to_csv.py input.jsonl  # outputs to input.csv
    python convert_jsonl_to_csv.py input.jsonl output.csv --delimiter "|"
    python convert_jsonl_to_csv.py input.jsonl output.csv --encoding utf-8
"""

import json
import csv
import argparse
import sys
from pathlib import Path
from typing import Dict, Any, Set, List, Optional


def get_fields(jsonl_file: Path) -> Set[str]:
    """Get all unique field names from all records in the JSONL file."""
    all_fields = []
    
    with open(jsonl_file, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
                
            try:
                record = json.loads(line)
                if isinstance(record, dict):
                    if not all_fields:
                        all_fields = record.keys()
                    elif all_fields != record.keys():
                        raise ValueError(f"Warning: Line {line_num} has different fields than previous lines")
                else:
                    raise ValueError(f"Warning: Line {line_num} is not a JSON object, skipping")
            except json.JSONDecodeError as e:
                raise ValueError(f"Warning: Invalid JSON on line {line_num}: {e}")
                continue
    
    return all_fields


def convert_jsonl_to_csv(
    input_file: Path, 
    output_file: Path, 
    delimiter: str = ',',
    encoding: str = 'utf-8'
) -> None:
    """Convert JSONL file to CSV format."""
    
    print(f"Converting {input_file} to {output_file}")
    
    # First pass: collect all possible field names
    print("Collecting all field names...")
    all_fields = get_fields(input_file)
    
    if not all_fields:
        print("No valid JSON objects found in the input file")
        return
    
    print(f"Found {len(all_fields)} unique fields: {', '.join(all_fields)}")
    
    # Second pass: write CSV
    print("Writing CSV file...")
    records_processed = 0
    
    with open(input_file, 'r', encoding=encoding) as infile, \
         open(output_file, 'w', newline='', encoding=encoding) as outfile:
        
        writer = csv.DictWriter(outfile, fieldnames=all_fields, delimiter=delimiter)
        writer.writeheader()
        
        for line_num, line in enumerate(infile, 1):
            line = line.strip()
            if not line:
                continue
                
            try:
                record = json.loads(line)
                if isinstance(record, dict):
                    # Fill missing fields with empty strings
                    csv_record = {field: record.get(field, '') for field in all_fields}
                    writer.writerow(csv_record)
                    records_processed += 1
                else:
                    print(f"Warning: Line {line_num} is not a JSON object, skipping")
            except json.JSONDecodeError as e:
                print(f"Warning: Invalid JSON on line {line_num}: {e}")
                continue
    
    print(f"Successfully converted {records_processed} records to CSV")
    print(f"Output saved to: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description="Convert JSONL files to CSV format",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s input.jsonl output.csv
  %(prog)s input.jsonl                    # outputs to input.csv
  %(prog)s input.jsonl output.csv --delimiter "|"
  %(prog)s input.jsonl output.csv --encoding utf-8
        """
    )
    
    parser.add_argument(
        'input_file',
        type=Path,
        help='Input JSONL file path'
    )
    
    parser.add_argument(
        'output_file',
        type=Path,
        nargs='?',
        help='Output CSV file path (default: input_file with .csv extension)'
    )
    
    parser.add_argument(
        '--delimiter',
        default=',',
        help='CSV delimiter (default: comma)'
    )
    
    parser.add_argument(
        '--encoding',
        default='utf-8',
        help='File encoding (default: utf-8)'
    )
    
    args = parser.parse_args()
    
    # Validate input file
    if not args.input_file.exists():
        print(f"Error: Input file '{args.input_file}' does not exist")
        sys.exit(1)
    
    if not args.input_file.suffix.lower() in ['.jsonl', '.json']:
        print(f"Warning: Input file '{args.input_file}' doesn't have .jsonl or .json extension")
    
    # Determine output file
    if args.output_file is None:
        args.output_file = args.input_file.with_suffix('.csv')
    
    # Create output directory if it doesn't exist
    args.output_file.parent.mkdir(parents=True, exist_ok=True)
    
    try:
        convert_jsonl_to_csv(
            args.input_file,
            args.output_file,
            args.delimiter,
            args.encoding
        )
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
