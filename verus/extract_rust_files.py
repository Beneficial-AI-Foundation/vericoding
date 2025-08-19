#!/usr/bin/env python3
import json
import os
import re

def extract_rust_files(json_file_path, output_dir="extracted_rust_files"):
    """
    Extract Rust code from JSON file and save as individual .rs files
    """
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    extracted_files = []
    
    with open(json_file_path, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
                
            try:
                # Parse JSON object
                data = json.loads(line)
                
                # Extract Rust code from 'y' field
                if 'y' in data and data['y']:
                    rust_code = data['y']
                    
                    # Generate filename based on function name or line number
                    filename = f"rust_file_{line_num:03d}.rs"
                    
                    # Try to extract function name for better filename
                    function_match = re.search(r'fn\s+(\w+)', rust_code)
                    if function_match:
                        func_name = function_match.group(1)
                        filename = f"{func_name}.rs"
                    
                    # Save to file
                    file_path = os.path.join(output_dir, filename)
                    with open(file_path, 'w', encoding='utf-8') as rust_file:
                        rust_file.write(rust_code)
                    
                    extracted_files.append({
                        'filename': filename,
                        'function_name': function_match.group(1) if function_match else None,
                        'line_number': line_num,
                        'dataset': data.get('dset', 'Unknown')
                    })
                    
                    print(f"Extracted: {filename}")
                    
            except json.JSONDecodeError as e:
                print(f"Error parsing JSON at line {line_num}: {e}")
            except Exception as e:
                print(f"Error processing line {line_num}: {e}")
    
    # Save summary
    summary_path = os.path.join(output_dir, "extraction_summary.txt")
    with open(summary_path, 'w', encoding='utf-8') as summary_file:
        summary_file.write(f"Extracted {len(extracted_files)} Rust files\n")
        summary_file.write("=" * 50 + "\n\n")
        
        for file_info in extracted_files:
            summary_file.write(f"File: {file_info['filename']}\n")
            if file_info['function_name']:
                summary_file.write(f"Function: {file_info['function_name']}\n")
            summary_file.write(f"Line: {file_info['line_number']}\n")
            summary_file.write(f"Dataset: {file_info['dataset']}\n")
            summary_file.write("-" * 30 + "\n")
    
    print(f"\nExtraction complete! {len(extracted_files)} files extracted to '{output_dir}'")
    print(f"Summary saved to: {summary_path}")
    
    return extracted_files

if __name__ == "__main__":
    json_file = "src/verus_specs/alpha-verus/mbpp.jsonl"
    extracted = extract_rust_files(json_file) 