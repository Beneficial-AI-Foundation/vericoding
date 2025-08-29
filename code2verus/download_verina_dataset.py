#!/usr/bin/env python3
"""
Download the Verina dataset from Hugging Face
"""

from datasets import load_dataset
import os
import json
from pathlib import Path

def download_verina_dataset():
    """Download and save the Verina dataset locally"""
    
    print("Loading Verina dataset from Hugging Face...")
    dataset = load_dataset("sunblaze-ucb/verina")
    
    # Create directory for the dataset
    verina_data_dir = Path("verina_dataset")
    verina_data_dir.mkdir(exist_ok=True)
    
    # Save dataset info
    info = {
        "dataset_name": "sunblaze-ucb/verina",
        "description": "Verina dataset containing Lean 4 code and specifications",
        "splits": list(dataset.keys()),
        "features": str(dataset[list(dataset.keys())[0]].features) if dataset else "No features found"
    }
    
    with open(verina_data_dir / "dataset_info.json", "w") as f:
        json.dump(info, f, indent=2)
    
    # Process each split
    for split_name, split_data in dataset.items():
        print(f"\nProcessing split: {split_name}")
        print(f"Number of examples: {len(split_data)}")
        
        split_dir = verina_data_dir / split_name
        split_dir.mkdir(exist_ok=True)
        
        # Save examples
        for idx, example in enumerate(split_data):
            example_file = split_dir / f"example_{idx:04d}.json"
            
            # Convert example to dictionary if it's not already
            if hasattr(example, 'to_dict'):
                example_dict = example.to_dict()
            else:
                example_dict = dict(example)
            
            with open(example_file, "w") as f:
                json.dump(example_dict, f, indent=2)
            
            # Also save Lean code separately if it exists
            if 'code' in example_dict or 'lean_code' in example_dict:
                lean_code = example_dict.get('code', example_dict.get('lean_code', ''))
                if lean_code:
                    lean_file = split_dir / f"example_{idx:04d}.lean"
                    with open(lean_file, "w") as f:
                        f.write(lean_code)
            
            if idx < 3:  # Print first few examples
                print(f"\nExample {idx}:")
                for key, value in example_dict.items():
                    if isinstance(value, str) and len(value) > 100:
                        print(f"  {key}: {value[:100]}...")
                    else:
                        print(f"  {key}: {value}")
        
        print(f"Saved {len(split_data)} examples in {split_dir}")
    
    print(f"\nDataset downloaded successfully to {verina_data_dir.absolute()}")
    
    # Create a summary
    summary_lines = [
        "# Verina Dataset Summary\n",
        f"Total splits: {len(dataset)}\n"
    ]
    
    for split_name, split_data in dataset.items():
        summary_lines.append(f"\n## {split_name} split")
        summary_lines.append(f"- Examples: {len(split_data)}")
        if split_data:
            summary_lines.append(f"- Features: {list(split_data.features.keys())}")
    
    with open(verina_data_dir / "SUMMARY.md", "w") as f:
        f.write("\n".join(summary_lines))

if __name__ == "__main__":
    download_verina_dataset()
