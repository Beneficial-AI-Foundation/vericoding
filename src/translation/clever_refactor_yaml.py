#!/usr/bin/env python3
import yaml
import os
import glob

def write_multiline_field(f, field_name, content):
    """Write a YAML field with |- decorator and proper indentation."""
    f.write(f"{field_name}: |-\n")
    if content:
        for line in content.split('\n'):
            f.write(f"  {line}\n")
    f.write("\n")

def write_vc_description(f, data):
    """Write the vc-description field."""
    problem_details = data.get('problem_details', '')
    write_multiline_field(f, "vc-description", problem_details)

def write_vc_preamble(f, data):
    """Write the vc-preamble field."""
    preamble = data.get('preamble', '')
    write_multiline_field(f, "vc-preamble", preamble)

def write_vc_helpers(f):
    """Write the vc-helpers field with the specified value."""
    f.write("vc-helpers: |-\n")
    f.write("  -- <vc-helpers>\n")
    f.write("  -- </vc-helpers>\n")
    f.write("\n")

def write_vc_code(f, data):
    """Write the vc-code field."""
    implementation_signature = data.get('implementation_signature', '')
    implementation = data.get('implementation', '')
    test_cases = data.get('test_cases', '')
    write_multiline_field(f, "vc-code", implementation_signature + "\n-- <vc-code>\n" + implementation + "\n-- </vc-code>\n\n" + test_cases)

def write_vc_spec(f, data):
    """Write the vc-spec field."""
    problem_spec = data.get('problem_spec', '')
    correctness_definition = data.get('correctness_definition', '')
    correctness_proof = data.get('correctness_proof', '')
    write_multiline_field(f, "vc-spec", problem_spec + "\n\n" + correctness_definition + "\n-- <vc-proof>\n" + correctness_proof + "\n-- </vc-proof>")

def write_vc_postamble(f, data):
    """Write the vc-postamble field."""
    postamble = data.get('postamble', '')
    test_cases = data.get('test_cases', '')
    write_multiline_field(f, "vc-postamble", test_cases + "\n\n" + postamble)

def transform_yaml_file(input_file, output_file):
    """Transform a YAML file according to the specified field mappings."""
    
    # Read the original YAML file
    with open(input_file, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    
    # Write the transformed YAML file with proper |- decorators
    with open(output_file, 'w', encoding='utf-8') as f:
        # Write each field using dedicated functions
        write_vc_description(f, data)
        write_vc_preamble(f, data)
        write_vc_helpers(f)
        write_vc_code(f, data)
        write_vc_spec(f, data)
        write_vc_postamble(f, data)

def main():
    # Get all YAML files in the humaneval_yaml directory
    input_dir = 'benchmarks/vericoding_raw/humaneval_yaml'
    output_dir = 'benchmarks/vericoding_raw/humaneval_yaml_transformed'
    
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    # Find all YAML files
    yaml_files = glob.glob(os.path.join(input_dir, '*.yaml'))
    
    print(f"Found {len(yaml_files)} YAML files to transform")
    
    # Transform each file
    for input_file in yaml_files:
        filename = os.path.basename(input_file)
        output_file = os.path.join(output_dir, filename)
        
        try:
            transform_yaml_file(input_file, output_file)
            print(f"Transformed: {filename}")
        except Exception as e:
            print(f"Error transforming {filename}: {e}")
    
    print(f"\nTransformation complete! Files saved to: {output_dir}")

if __name__ == "__main__":
    main()
