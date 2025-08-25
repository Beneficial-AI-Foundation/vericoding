"""Item processing and async logic for code2verus"""
import asyncio
import random
from pathlib import Path
from pydantic_ai import ModelHTTPError
import logfire
import yaml

from code2verus.config import ARTIFACTS
from code2verus.agent import translate_code_to_verus
from code2verus.verification import verify_verus_code
from code2verus.success_tracker import save_success_info, is_sample_already_successful
from code2verus.benchmarks import is_flat_structure


async def process_item(
    idx: int, item: dict, source_language: str = "dafny", benchmark_name: str = "dafnybench", max_retries: int = 32, base_delay: float = 5.0, is_flat: bool = False, is_yaml: bool = False
) -> dict:
    """Process a single item from the dataset with exponential backoff"""

    suffix = '.rs' if not is_yaml else '.yaml'

    # Handle different dataset structures
    if "ground_truth" in item:
        # DafnyBench format
        source_code = item["ground_truth"]
        source_filename = Path(item["test_file"])
        # Preserve the directory structure but change extension to .rs
        relative_path = source_filename.with_suffix(suffix)
    elif "org_input" in item:
        # ReForm-DafnyComp-Benchmark format
        source_code = item["org_input"]
        # Generate filename from item ID, preserve any directory structure
        source_filename = Path(f"item_{item.get('org_input_id', idx)}.dfy")
        relative_path = source_filename.with_suffix(suffix)
    elif "id" in item and "lean_code" in item:
        # Verina format (sunblaze-ucb/verina)
        source_code = item["lean_code"]
        # Use the actual ID from the dataset (e.g., "verina_basic_70")
        source_filename = Path(f"{item['id']}.lean")
        # Create a directory for each item
        relative_path = Path(item['id']) / source_filename.with_suffix(suffix).name
    else:
        # Fallback for unknown formats
        source_code = item.get("code", item.get("source", ""))
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix(suffix)
    
    artifact_path = ARTIFACTS / benchmark_name / relative_path.parent
    output_filename = relative_path.name

    # Check if this sample already succeeded
    if is_sample_already_successful(relative_path.with_suffix(''), benchmark_name, source_filename.name, is_flat):
        logfire.info(f"Skipping item {idx + 1}: {source_filename} (already successful)")
        return {"path": artifact_path, "success": True}

    logfire.info(f"Processing item {idx + 1}: {source_filename} ({source_language})")
    artifact_path.mkdir(parents=True, exist_ok=True)

    # Exponential backoff retry logic
    for attempt in range(max_retries + 1):
        try:
            verus_code, num_iterations = await translate_code_to_verus(source_code, source_language, is_yaml)
            verus_output_path = artifact_path / output_filename
            with open(verus_output_path, "w") as verus_file:
                verus_file.write(verus_code)
            logfire.info(f"Generated Verus code saved to: {verus_output_path}")

            # Use async verification
            verification_success, verification_output, verification_error = await verify_verus_code(verus_code, is_yaml)

            info = {
                "success": verification_success,
                "num_iterations": num_iterations,
                "verification_output": verification_output,
                "verification_error": verification_error,
            }
            
            # Save success info using the appropriate method (JSON for flat, YAML for hierarchical)
            save_success_info(artifact_path, source_filename.name, info, benchmark_name, is_flat)

            return {"path": artifact_path, "success": verification_success}

        except ModelHTTPError as exc:
            if attempt == max_retries:
                logfire.info(
                    f"Failed to process item {idx + 1} after {max_retries} retries: {exc}"
                )
                raise

            # Calculate delay with exponential backoff and jitter
            delay = base_delay * (2**attempt) + random.uniform(0, 1)
            logfire.info(
                f"Rate limited on item {idx + 1}, attempt {attempt + 1}/{max_retries + 1}. Retrying in {delay:.2f}s..."
            )
            await asyncio.sleep(delay)
    return {"path": artifact_path, "success": False}


async def check_existing_success(idx: int, item: dict, benchmark_name: str, is_flat: bool = False) -> bool:
    """Async helper to check if a sample is already successful"""
    # Handle different dataset structures
    if "test_file" in item:
        # DafnyBench format
        source_filename = Path(item["test_file"])
        # Preserve directory structure but remove extension for checking
        relative_path = source_filename.with_suffix('')
    elif "org_input" in item:
        # ReForm-DafnyComp-Benchmark format
        source_filename = Path(f"item_{item.get('org_input_id', idx)}.dfy")
        relative_path = source_filename.with_suffix('')
    elif "id" in item and "lean_code" in item:
        # Verina format (sunblaze-ucb/verina)
        source_filename = Path(f"{item['id']}.lean")
        # Use directory structure for each item
        relative_path = Path(item['id'])
    elif "filename" in item:
        # Local file format
        source_filename = Path(item["filename"])
        relative_path = source_filename.with_suffix('')
    else:
        # Fallback for unknown formats
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix('')
        
    return is_sample_already_successful(relative_path, benchmark_name, source_filename.name, is_flat)


async def main_async(benchmark: str = "wendy-sun/DafnyBench", split: str = "test", source_language: str = "dafny", max_concurrent: int = 3, file_pattern: str = "*.dfy") -> None:
    """Async main function for parallel processing"""
    from code2verus.benchmarks import load_benchmark, is_flat_structure
    
    print("Code2Verus translator initialized!")

    # Load the dataset
    dataset = load_benchmark(benchmark, split, file_pattern)
    
    # Extract benchmark name for artifact path
    # Handle both Hugging Face format (user/dataset) and local paths
    if Path(benchmark).exists() and Path(benchmark).is_dir():
        # For local paths, use the folder name
        benchmark_name = Path(benchmark).name.lower().replace("-", "_")
    else:
        # For Hugging Face datasets
        benchmark_name = benchmark.split("/")[-1].lower().replace("-", "")

    # Check if we have a flat structure (all files in same directory)
    is_flat = is_flat_structure(dataset, benchmark_name)
    if is_flat:
        print(f"Detected flat folder structure - using consolidated success tracking")

    # Check for existing successful samples in parallel
    print("Checking for existing successful samples...")
    existing_success_checks = [
        check_existing_success(idx, item, benchmark_name, is_flat) 
        for idx, item in enumerate(dataset)
    ]
    existing_success_results = await asyncio.gather(*existing_success_checks)
    skipped_count = sum(existing_success_results)

    # Limit concurrent API calls to prevent rate limiting
    semaphore = asyncio.Semaphore(max_concurrent)

    is_yaml = file_pattern.endswith("yaml")

    async def process_with_semaphore(idx: int, item: dict) -> dict:
        async with semaphore:
            return await process_item(idx, item, source_language, benchmark_name, max_retries=32, base_delay=5.0, is_flat=is_flat, is_yaml=is_yaml)

    item_processes = [
        process_with_semaphore(idx, item) for idx, item in enumerate(dataset)
    ]
    # Process all items in parallel using asyncio.gather and list comprehension
    results = await asyncio.gather(*item_processes)

    with open(ARTIFACTS / f"{benchmark_name}_results.yml", "w") as results_file:
        yaml.dump(results, results_file)

    # Calculate statistics
    total_successful = sum(res["success"] for res in results)
    percentage_successful = total_successful / len(results)

    print("Results:")
    print(f"  Successful files: {total_successful}")
    print(f"  Total files: {len(results)}")
    print(f"  Overall success rate: {100 * percentage_successful:.1f}%")
