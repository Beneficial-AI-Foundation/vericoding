#!/usr/bin/env python3
"""
Normalize Lean YAML structure: merge vc-implementation/vc-signature into
vc-definitions and vc-proof/vc-condition into vc-theorems, with whitespace tidy.
"""

from pathlib import Path
import sys

# Add src directory to path to import convert_from_yaml
sys.path.append(str(Path(__file__).parent.parent))
from convert_from_yaml import spec_to_yaml


def normalize_section_content(content: str) -> str:
    """Normalize section content by removing leading empty lines and reducing consecutive empty lines to one."""
    if not content:
        return ""

    lines = content.split("\n")

    # Remove empty lines at the start
    while lines and lines[0].strip() == "":
        lines = lines[1:]

    # Reduce consecutive empty lines to single empty lines
    normalized_lines = []
    prev_empty = False

    for line in lines:
        if line.strip() == "":
            if not prev_empty:
                normalized_lines.append("")
                prev_empty = True
        else:
            normalized_lines.append(line)
            prev_empty = False

    # Join and apply rstrip
    return "\n".join(normalized_lines).rstrip()


def process_yaml_file(file_path: Path) -> None:
    """Process a single YAML file: merge signature/implementation into definitions and condition/proof into theorems; normalize sections."""
    try:
        # Import ruamel.yaml here to avoid circular imports
        from ruamel.yaml import YAML

        # Read the YAML file with ruamel.yaml to preserve structure
        yaml_loader = YAML()
        yaml_loader.preserve_quotes = True

        with open(file_path, "r", encoding="utf-8") as f:
            spec = yaml_loader.load(f)

        if spec is None:
            print(f"Warning: {file_path} is empty or invalid YAML")
            return

        # Check for vc-implementation/vc-signature vs vc-definitions validation
        has_implementation_signature = (
            "vc-implementation" in spec and "vc-signature" in spec
        )
        has_definitions = "vc-definitions" in spec

        if (has_implementation_signature and has_definitions) or (
            not has_implementation_signature and not has_definitions
        ):
            raise ValueError(
                f"Invalid YAML structure in {file_path}: Must have either (vc-implementation AND vc-signature) OR vc-definitions, but not both or neither"
            )

        # Process vc-implementation and vc-signature if they exist
        if has_implementation_signature:
            implementation = spec["vc-implementation"]
            signature = spec["vc-signature"]

            # Concatenate with newline
            combined_content = f"{signature}\n{implementation}"

            # Remove lines containing only "-- <vc-implementation>" or "-- </vc-implementation>" after stripping
            lines = combined_content.split("\n")
            filtered_lines = []
            for line in lines:
                stripped = line.strip()
                if stripped not in [
                    "-- <vc-implementation>",
                    "-- </vc-implementation>",
                ]:
                    filtered_lines.append(line)

            # Replace vc-implementation with the processed content and remove vc-signature
            spec["vc-definitions"] = normalize_section_content(
                "\n".join(filtered_lines)
            )
            del spec["vc-implementation"]
            del spec["vc-signature"]

        # Check for vc-proof/vc-condition vs vc-theorems validation
        has_proof_condition = "vc-proof" in spec and "vc-condition" in spec
        has_theorems = "vc-theorems" in spec

        if (has_proof_condition and has_theorems) or (
            not has_proof_condition and not has_theorems
        ):
            raise ValueError(
                f"Invalid YAML structure in {file_path}: Must have either (vc-proof AND vc-condition) OR vc-theorems, but not both or neither"
            )

        # Process vc-proof and vc-condition if they exist
        if has_proof_condition:
            proof = spec["vc-proof"]
            condition = spec["vc-condition"]

            # Concatenate with newline
            combined_content = f"{condition}\n{proof}"

            # Remove lines containing only "-- <vc-proof>" or "-- </vc-proof>" after stripping
            lines = combined_content.split("\n")
            filtered_lines = []
            for line in lines:
                stripped = line.strip()
                if stripped not in ["-- <vc-proof>", "-- </vc-proof>"]:
                    filtered_lines.append(line)

            # Replace vc-proof with the processed content and remove vc-condition
            spec["vc-theorems"] = normalize_section_content("\n".join(filtered_lines))
            del spec["vc-proof"]
            del spec["vc-condition"]

        # Normalize all other sections
        for key, value in spec.items():
            if key not in [
                "vc-proof",
                "vc-condition",
                "vc-implementation",
                "vc-signature",
            ] and isinstance(value, str):
                spec[key] = normalize_section_content(value)

        # Get the required keys in the order they appeared in the original file
        required_keys = [
            "vc-description",
            "vc-preamble",
            "vc-helpers",
            "vc-definitions",
            "vc-theorems",
            "vc-postamble",
        ]

        # Write back to the file using spec_to_yaml to preserve structure
        spec_to_yaml(spec, file_path, required_keys)

        # print(f"Processed: {file_path}")

    except Exception as e:
        print(f"Error processing {file_path}: {e}")


def main():
    """Main function to process all YAML files in directories with yaml subfolders."""
    # Get the lean benchmarks directory
    lean_dir = Path("benchmarks/lean")

    if not lean_dir.exists():
        print(f"Error: Directory {lean_dir} not found")
        return

    total_files_processed = 0

    # Loop through all immediate folders in the lean directory
    for folder in [lean_dir / "verified_cogen"]:
        if folder.is_dir():
            yaml_subfolder = folder / "yaml"

            # Check if this folder has a yaml subfolder
            if yaml_subfolder.exists() and yaml_subfolder.is_dir():
                print(f"Processing YAML files in {folder.name}/yaml/")

                # Find all YAML files in the yaml subfolder
                yaml_files = list(yaml_subfolder.glob("*.yaml"))

                if not yaml_files:
                    print(f"  No YAML files found in {yaml_subfolder}")
                    continue

                print(f"  Found {len(yaml_files)} YAML files to process")

                # Process each file
                count = 0
                for yaml_file in yaml_files:
                    count += 1
                    if count % 100 == 0:
                        print(f"  Processing {count} of {len(yaml_files)}")
                    process_yaml_file(yaml_file)
                    total_files_processed += 1

                print(f"  Completed processing {folder.name}/yaml/")

    print(f"Processing complete! Total files processed: {total_files_processed}")


if __name__ == "__main__":
    main()
