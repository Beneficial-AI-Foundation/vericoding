#!/usr/bin/env python3
from ruamel.yaml import YAML
import os
import glob
from convert_from_yaml import spec_to_yaml


def build_vc_description(data):
    """Build the vc-description field."""
    return data.get("problem_details", "").rstrip()


def build_vc_preamble(data):
    """Build the vc-preamble field."""
    return data.get("preamble", "").rstrip()


def build_vc_helpers():
    """Build the vc-helpers field with the specified value."""
    return "-- <vc-helpers>\n-- </vc-helpers>"


def build_vc_signature(data):
    """Build the vc-signature field."""
    return data.get("implementation_signature", "").rstrip()


def build_vc_implementation(data):
    """Build the vc-implementation field."""
    implementation = data.get("implementation", "").rstrip()
    return "-- <vc-code>\n" + implementation + "\n-- </vc-code>"


def build_vc_condition(data):
    """Build the vc-condition field."""
    problem_spec = data.get("problem_spec", "").rstrip()
    correctness_definition = data.get("correctness_definition", "").rstrip()
    return problem_spec + "\n\n" + correctness_definition


def build_vc_proof(data):
    """Build the vc-spec field."""
    correctness_proof = data.get("correctness_proof", "").rstrip()
    return "-- <vc-proof>\n" + correctness_proof + "\n-- </vc-proof>"


def build_vc_postamble(data):
    """Build the vc-postamble field."""
    test_cases = data.get("test_cases", "").rstrip()
    postamble = data.get("postamble", "").rstrip()
    return test_cases + "\n\n" + postamble


def transform_yaml_file(input_file, output_file):
    """Transform a YAML file according to the specified field mappings using spec_to_yaml."""

    # Initialize ruamel.yaml
    yaml = YAML()
    yaml.preserve_quotes = True  # Preserve original formatting

    # Read the original YAML file
    with open(input_file, "r", encoding="utf-8") as f:
        data = yaml.load(f)

    # Build the spec object
    spec = {
        "vc-description": build_vc_description(data),
        "vc-preamble": build_vc_preamble(data),
        "vc-helpers": build_vc_helpers(),
        "vc-signature": build_vc_signature(data),
        "vc-implementation": build_vc_implementation(data),
        "vc-condition": build_vc_condition(data),
        "vc-proof": build_vc_proof(data),
        "vc-postamble": build_vc_postamble(data),
    }

    # Define the required keys in the desired order
    required_keys = [
        "vc-description",
        "vc-preamble",
        "vc-helpers",
        "vc-signature",
        "vc-implementation",
        "vc-condition",
        "vc-proof",
        "vc-postamble",
    ]

    # Write the transformed YAML file using spec_to_yaml
    spec_to_yaml(spec, output_file, required_keys=required_keys)


def main():
    # Get all YAML files in the humaneval_yaml directory
    input_dir = "benchmarks/vericoding_raw/humaneval_yaml"
    output_dir = "benchmarks/vericoding_raw/humaneval_yaml_transformed"

    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)

    # Find all YAML files
    yaml_files = glob.glob(os.path.join(input_dir, "*.yaml"))

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
