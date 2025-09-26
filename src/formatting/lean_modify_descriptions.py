#!/usr/bin/env python3
"""
Normalize Lean YAML: wrap vc-description in a doc comment and
tidy whitespace/markers across sections.
"""

from pathlib import Path
import sys

# Add src directory to path to import convert_from_yaml
sys.path.append(str(Path(__file__).parent.parent))
from convert_from_yaml import spec_to_yaml


def sanitize_description_for_block_comment(text: str) -> str:
    """Avoid accidental nested block comments inside '/- ... -/'.

    We replace occurrences of '+/-' with the single glyph '±'. This preserves
    meaning while preventing '/-' from being parsed as a nested comment start.
    """
    if not isinstance(text, str) or not text:
        return text
    return text.replace("+/-", "±")


def normalize_section_content(content: str) -> str:
    """Normalize section content by removing leading empty lines and reducing consecutive empty lines to one."""
    if not content:
        return ""

    lines = content.split("\n")

    # Remove empty lines at the start
    while lines and lines[0].strip() == "":
        lines = lines[1:]

    # Reduce consecutive empty lines to single empty lines and apply line transformations
    normalized_lines = []
    prev_empty = False

    for line in lines:
        if line.strip() == "":
            if not prev_empty:
                normalized_lines.append("")
                prev_empty = True
        else:
            # Apply line transformations
            transformed_line = line

            # Replace /-- with /- at the beginning of the line
            if transformed_line.startswith("/--"):
                transformed_line = "/-" + transformed_line[3:]

            # Add -- prefix to lines starting with #guard_msgs
            if transformed_line.startswith("#guard_msgs"):
                transformed_line = "-- " + transformed_line

            # Add -- prefix to lines starting with #eval
            if transformed_line.startswith("#eval"):
                transformed_line = "-- " + transformed_line

            normalized_lines.append(transformed_line)
            prev_empty = False

    # Join and apply rstrip
    return "\n".join(normalized_lines).rstrip()


def process_yaml_file(file_path: Path) -> None:
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

        # Process vc-description if it exists
        if "vc-description" in spec:
            description = sanitize_description_for_block_comment(spec["vc-description"])

            # Check if value starts with /-
            if description.startswith("/-"):
                print(
                    f"vc-description in {file_path} already starts with '/-', which is not allowed"
                )
                return

            # Check if value ends with -/
            if description.endswith("-/"):
                print(
                    f"vc-description in {file_path} already ends with '-/', which is not allowed"
                )
                return

            # Wrap the description with /-\n at start and -/\n at end
            spec["vc-description"] = f"/-\n{description}\n-/\n"

        else:
            print(f"vc-description not found in {file_path}")
            return

        # Normalize all other sections
        for key, value in spec.items():
            if key not in ["vc-description"] and isinstance(value, str):
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
        return


def main():
    """Main function to process all YAML files in directories with yaml subfolders."""
    # Get the lean benchmarks directory
    lean_dir = Path("benchmarks/lean")

    if not lean_dir.exists():
        print(f"Error: Directory {lean_dir} not found")
        return

    total_files_processed = 0

    # Loop through all immediate folders in the lean directory
    for folder in [lean_dir / "apps_train"]:
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
