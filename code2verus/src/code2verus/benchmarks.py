"""Benchmark and dataset loading functionality for code2verus"""
from pathlib import Path
from datasets import load_dataset
import logfire


def load_local_benchmark(folder_path: Path, file_pattern: str = "*.dfy"):
    """Load benchmark dataset from a local folder"""
    folder_path = Path(folder_path)
    
    if not folder_path.exists():
        raise ValueError(f"Folder {folder_path} does not exist")
    
    items = []
    # Support both single pattern and multiple patterns
    patterns = [file_pattern] if isinstance(file_pattern, str) else file_pattern
    
    for pattern in patterns:
        # Use rglob for recursive search if pattern contains **
        glob_func = folder_path.rglob if "**" in pattern else folder_path.glob
        for file_path in sorted(glob_func(pattern)):
            if file_path.is_file():
                with open(file_path, "r") as f:
                    content = f.read()
                
                # Create item dict with consistent structure
                item = {
                    "ground_truth": content,
                    "test_file": str(file_path.relative_to(folder_path.parent)),
                    "source_path": str(file_path),
                    "filename": file_path.name,
                }
                items.append(item)
    
    logfire.info(f"Loaded {len(items)} files from {folder_path} with pattern(s): {patterns}")
    return items


def load_benchmark(benchmark: str = "wendy-sun/DafnyBench", split: str = "test", file_pattern: str = "*.dfy"):
    """Load the specified benchmark dataset from Hugging Face or local folder"""
    # Check if benchmark is a local path
    potential_path = Path(benchmark)
    if potential_path.exists() and potential_path.is_dir():
        logfire.info(f"Loading local benchmark from {benchmark}...")
        return load_local_benchmark(potential_path, file_pattern)
    elif "/" in benchmark and not benchmark.startswith(("http://", "https://")):
        # Check parent paths in case of relative path
        if (Path.cwd() / benchmark).exists() and (Path.cwd() / benchmark).is_dir():
            logfire.info(f"Loading local benchmark from {benchmark}...")
            return load_local_benchmark(Path.cwd() / benchmark, file_pattern)
    
    # Otherwise treat as Hugging Face dataset
    logfire.info(f"Loading {benchmark} dataset from Hugging Face (split: {split})...")
    dataset = load_dataset(benchmark, split=split)
    return dataset


def is_flat_structure(dataset, benchmark_name: str) -> bool:
    """Check if the dataset represents a flat folder structure (all files in same directory)"""
    if not dataset:
        return False
        
    # For local datasets, check if all files are in the same parent directory
    if isinstance(dataset, list) and "source_path" in dataset[0]:
        # Get all parent directories
        parent_dirs = set()
        for item in dataset:
            source_path = Path(item["source_path"])
            parent_dirs.add(source_path.parent)
        
        # If all files share the same parent directory, it's flat
        return len(parent_dirs) == 1
    
    return False
