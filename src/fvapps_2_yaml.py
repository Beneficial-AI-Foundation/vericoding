import datasets
from pathlib import Path
from typing import Dict, Any, List, Tuple
import re
from ruamel.yaml import YAML


def load_fvapps_dataset():
    """Load the quinn-dougherty/fvapps dataset from Hugging Face."""
    dataset = datasets.load_dataset("quinn-dougherty/fvapps", split="train")
    return dataset


def parse_lean_spec(spec_text: str) -> Tuple[List[str], str, List[str]]:
    """Parse Lean spec to extract defs and theorems.

    Returns:
        (preceding_defs, last_def, theorems)
    """
    if not spec_text:
        return [], "", []

    # Split by lines and reconstruct complete definitions/theorems
    lines = spec_text.strip().split("\n")

    # Track current item being built
    current_item = []
    items = []
    in_multiline = False

    for line in lines:
        stripped = line.strip()

        # Check if starting a new def or theorem
        if (
            stripped.startswith("def ") or stripped.startswith("theorem ")
        ) and not in_multiline:
            # Save previous item if exists
            if current_item:
                items.append("\n".join(current_item))
            current_item = [line]
            in_multiline = True
        else:
            # Continue building current item
            current_item.append(line)

            # Simple heuristic: if line doesn't end with incomplete syntax, might be end
            if stripped and not any(
                stripped.endswith(char) for char in [":=", ":", "∧", "∨", "→", "↔"]
            ):
                # Check for balanced parentheses/brackets as another heuristic
                paren_balance = stripped.count("(") - stripped.count(")")
                bracket_balance = stripped.count("[") - stripped.count("]")
                if paren_balance == 0 and bracket_balance == 0:
                    in_multiline = False

    # Don't forget the last item
    if current_item:
        items.append("\n".join(current_item))

    # Separate defs from theorems
    defs = []
    theorems = []

    for item in items:
        if item.strip().startswith("def "):
            defs.append(item)
        elif item.strip().startswith("theorem "):
            theorems.append(item)

    # Split defs: all but last go to preamble, last goes to definitions
    if defs:
        preceding_defs = defs[:-1]
        last_def = defs[-1]
    else:
        preceding_defs = []
        last_def = ""

    return preceding_defs, last_def, theorems


def convert_sample_to_yaml(sample: Dict[str, Any]) -> str:
    """Convert a single dataset sample to YAML format with vc-* schema."""
    from ruamel.yaml.scalarstring import LiteralScalarString
    
    # Map FVAPPS columns to vc-* schema fields

    # vc-description maps from apps_question
    description = sample.get("apps_question", "")

    # Parse the spec field to extract defs and theorems
    spec = sample.get("spec", "")
    preceding_defs, last_def, spec_theorems = parse_lean_spec(spec)

    # Build vc-preamble from preceding defs only
    preamble_parts = []
    if preceding_defs:
        preamble_parts.extend(preceding_defs)
    preamble = "\n\n".join(preamble_parts)

    # vc-definitions gets the last def
    definitions = last_def

    # vc-theorems combines parsed theorems + units
    units = sample.get("units", "")
    theorem_parts = []
    if spec_theorems:
        theorem_parts.extend(spec_theorems)
    if units:
        theorem_parts.append(units)
    theorems = "\n\n".join(theorem_parts)

    # vc-postamble describes apps_difficulty and assurance_level
    difficulty = sample.get("apps_difficulty", "")
    assurance = sample.get("assurance_level", "")
    postamble_parts = []
    if difficulty:
        postamble_parts.append(f"-- Apps difficulty: {difficulty}")
    if assurance:
        postamble_parts.append(f"-- Assurance level: {assurance}")
    postamble = "\n".join(postamble_parts)

    # Create YAML content with multiline strings as literal block scalars
    yaml_content = {
        "vc-description": LiteralScalarString(description),
        "vc-preamble": LiteralScalarString(preamble),
        "vc-helpers": LiteralScalarString("-- <vc-helpers>\n-- </vc-helpers>"),
        "vc-definitions": LiteralScalarString(definitions),
        "vc-theorems": LiteralScalarString(theorems),
        "vc-postamble": LiteralScalarString(postamble),
    }

    # Use ruamel.yaml to dump with proper formatting
    yaml = YAML()
    yaml.preserve_quotes = True
    yaml.default_flow_style = False
    yaml.allow_unicode = True
    
    from io import StringIO
    stream = StringIO()
    yaml.dump(yaml_content, stream)
    return stream.getvalue()


def save_samples_as_yaml(dataset, output_dir: str = "benchmarks/lean/fvapps"):
    """Save each sample from the dataset as a separate YAML file."""
    output_path = Path(output_dir)
    output_path.mkdir(exist_ok=True)

    # Handle dataset structure - FVAPPS only has train split
    if hasattr(dataset, "items"):
        # Multiple splits case
        splits_to_process = dataset.items()
    else:
        # Single split case (likely just train)
        splits_to_process = [("train", dataset)]

    for split_name, split_data in splits_to_process:
        split_dir = output_path / split_name
        split_dir.mkdir(exist_ok=True)

        for idx, sample in enumerate(split_data):
            yaml_content = convert_sample_to_yaml(sample)
            filename = f"sample_{idx:06d}.yaml"
            filepath = split_dir / filename

            with open(filepath, "w", encoding="utf-8") as f:
                f.write(yaml_content)

        print(f"Saved {len(split_data)} samples to {split_dir}")


def main():
    """Main function to load dataset and convert to YAML files."""
    print("Loading quinn-dougherty/fvapps dataset...")
    dataset = load_fvapps_dataset()

    print("Converting samples to YAML files...")
    save_samples_as_yaml(dataset)

    print("Conversion complete!")


if __name__ == "__main__":
    main()
