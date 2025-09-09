"""Item processing and async logic for code2verus"""

import asyncio
import random
from pathlib import Path
from pydantic_ai import ModelHTTPError
import logfire
import yaml

from code2verus.config import ARTIFACTS, cfg
from code2verus.agent import translate_code_to_verus
from code2verus.verification import verify_verus_code
from code2verus.success_tracker import save_success_info, is_sample_already_successful


def derive_output_path(
    benchmark_path: str, benchmark_name: str, is_yaml: bool = False
) -> Path:
    """Derive the output path based on the benchmark input path.

    For benchmarks under 'benchmarks/lean/<name>/', output goes to 'benchmarks/verus/<name>/'
    For other paths, falls back to the current ARTIFACTS behavior.
    """
    benchmark_path_obj = Path(benchmark_path).resolve()

    # Check if this is a path under benchmarks/lean/
    if "benchmarks" in benchmark_path_obj.parts and "lean" in benchmark_path_obj.parts:
        # Find the benchmarks and lean parts in the path
        parts = list(benchmark_path_obj.parts)
        try:
            benchmarks_idx = parts.index("benchmarks")
            lean_idx = parts.index("lean", benchmarks_idx)

            # The benchmark name should be the next part after 'lean'
            if lean_idx + 1 < len(parts):
                lean_benchmark_name = parts[lean_idx + 1]

                # Build new path: benchmarks/verus/<lean_benchmark_name>
                base_path = (
                    Path(*parts[: benchmarks_idx + 1]) / "verus" / lean_benchmark_name
                )

                # Add subfolder based on file type
                if is_yaml:
                    return base_path / "yaml"
                else:
                    return base_path / "files"
        except (ValueError, IndexError):
            pass

    # Fallback to current behavior for non-lean benchmarks
    return ARTIFACTS / benchmark_name


async def process_item(
    idx: int,
    item: dict,
    source_language: str = "dafny",
    benchmark_name: str = "dafnybench",
    max_retries: int | None = None,
    base_delay: float = 5.0,
    is_flat: bool = False,
    is_yaml: bool = False,
    benchmark_path: str = "",
) -> dict:
    """Process a single item from the dataset with exponential backoff"""

    # Use config value if max_retries not provided, with fallback to 32
    if max_retries is None:
        max_retries = cfg.get("max_retries", 32)

    # Ensure max_retries is a valid integer
    if max_retries is None or max_retries <= 0:
        max_retries = 32

    # Type assertion to help type checker
    assert isinstance(max_retries, int)

    suffix = ".rs" if not is_yaml else ".yaml"

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
        relative_path = Path(item["id"]) / source_filename.with_suffix(suffix).name
    else:
        # Fallback for unknown formats
        source_code = item.get("code", item.get("source", ""))
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix(suffix)

    # Use the new path derivation logic
    artifact_base_path = derive_output_path(benchmark_path, benchmark_name, is_yaml)
    artifact_path = artifact_base_path / relative_path.parent
    output_filename = relative_path.name

    # Check if this sample already succeeded
    if is_sample_already_successful(
        relative_path.with_suffix(""),
        benchmark_name,
        source_filename.name,
        is_flat,
        benchmark_path,
    ):
        logfire.info(f"Skipping item {idx + 1}: {source_filename} (already successful)")
        return {"path": artifact_path, "success": True}

    logfire.info(f"Processing item {idx + 1}: {source_filename} ({source_language})")

    artifact_path.mkdir(parents=True, exist_ok=True)

    # Exponential backoff retry logic
    for attempt in range(max_retries + 1):
        try:
            (
                verus_code,
                num_iterations,
                rust_for_verification,
            ) = await translate_code_to_verus(source_code, source_language, is_yaml)

            logfire.info(f"Translation took {num_iterations} iterations")

            # Do a final verification to get the verification status for reporting
            # (the agent already did verification during iterations, but we need the final status)
            (
                verification_success,
                verification_output,
                verification_error,
            ) = await verify_verus_code(
                rust_for_verification,
                is_yaml,
                output_filename,
                benchmark_name,
                benchmark_path,
            )

            # Determine subfolder based on compilation success
            compilation_status = (
                "compiling" if verification_success else "non_compiling"
            )

            # Save the main output (YAML for YAML files, Rust for regular files) in appropriate subfolder
            status_artifact_path = artifact_path / compilation_status
            status_artifact_path.mkdir(parents=True, exist_ok=True)
            verus_output_path = status_artifact_path / output_filename
            with open(verus_output_path, "w") as verus_file:
                verus_file.write(verus_code)
            logfire.info(f"Generated Verus code saved to: {verus_output_path}")

            # For YAML files, also save the Rust code in the files folder for verification
            if is_yaml:
                # Create the files folder equivalent path with compilation status
                files_path = derive_output_path(
                    benchmark_path, benchmark_name, is_yaml=False
                )
                rust_status_path = (
                    files_path / relative_path.parent / compilation_status
                )
                rust_output_path = (
                    rust_status_path / Path(output_filename).with_suffix(".rs").name
                )
                rust_output_path.parent.mkdir(parents=True, exist_ok=True)

                with open(rust_output_path, "w") as rust_file:
                    rust_file.write(rust_for_verification)
                logfire.info(f"Generated Rust code saved to: {rust_output_path}")

            # Debug logging for verification results
            logfire.info(
                f"Verification completed for item {idx + 1}: success={verification_success}"
            )
            if not verification_success:
                logfire.info(f"Verification failed for item {idx + 1}:")
                if verification_error:
                    logfire.info(f"  Error: {verification_error}")
                if verification_output:
                    logfire.info(f"  Output: {verification_output}")

            info = {
                "success": verification_success,
                "num_iterations": num_iterations,
                "verification_output": verification_output,
                "verification_error": verification_error,
            }

            # Save success info using the appropriate method (JSON for flat, YAML for hierarchical)
            save_success_info(
                artifact_path,
                source_filename.name,
                info,
                benchmark_name,
                is_flat,
                benchmark_path,
            )

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


async def check_existing_success(
    idx: int,
    item: dict,
    benchmark_name: str,
    is_flat: bool = False,
    benchmark_path: str = "",
) -> bool:
    """Async helper to check if a sample is already successful"""
    # Handle different dataset structures
    if "test_file" in item:
        # DafnyBench format
        source_filename = Path(item["test_file"])
        # Preserve directory structure but remove extension for checking
        relative_path = source_filename.with_suffix("")
    elif "org_input" in item:
        # ReForm-DafnyComp-Benchmark format
        source_filename = Path(f"item_{item.get('org_input_id', idx)}.dfy")
        relative_path = source_filename.with_suffix("")
    elif "id" in item and "lean_code" in item:
        # Verina format (sunblaze-ucb/verina)
        source_filename = Path(f"{item['id']}.lean")
        # Use directory structure for each item
        relative_path = Path(item["id"])
    elif "filename" in item:
        # Local file format
        source_filename = Path(item["filename"])
        relative_path = source_filename.with_suffix("")
    else:
        # Fallback for unknown formats
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix("")

    return is_sample_already_successful(
        relative_path, benchmark_name, source_filename.name, is_flat, benchmark_path
    )


async def main_async(
    benchmark: str = "wendy-sun/DafnyBench",
    split: str = "test",
    source_language: str = "dafny",
    max_concurrent: int = 3,
    file_pattern: str = "*.dfy",
) -> None:
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
        print("Detected flat folder structure - using consolidated success tracking")

    # Check for existing successful samples in parallel
    print("Checking for existing successful samples...")
    existing_success_checks = [
        check_existing_success(idx, item, benchmark_name, is_flat, benchmark)
        for idx, item in enumerate(dataset)
    ]
    existing_success_results = await asyncio.gather(*existing_success_checks)
    _skipped_count = sum(existing_success_results)

    # Limit concurrent API calls to prevent rate limiting
    semaphore = asyncio.Semaphore(max_concurrent)

    is_yaml = file_pattern.endswith("yaml")

    async def process_with_semaphore(idx: int, item: dict) -> dict:
        async with semaphore:
            return await process_item(
                idx,
                item,
                source_language,
                benchmark_name,
                base_delay=5.0,
                is_flat=is_flat,
                is_yaml=is_yaml,
                benchmark_path=benchmark,
            )

    item_processes = [
        process_with_semaphore(idx, item) for idx, item in enumerate(dataset)
    ]
    # Process all items in parallel using asyncio.gather and list comprehension
    results = await asyncio.gather(*item_processes)

    # Use the new path derivation for results file as well
    results_base_path = derive_output_path(benchmark, benchmark_name, False)
    results_file_path = results_base_path / f"{benchmark_name}_results.yml"
    results_file_path.parent.mkdir(parents=True, exist_ok=True)

    with open(results_file_path, "w") as results_file:
        yaml.dump(results, results_file)

    # Calculate statistics
    total_successful = sum(res["success"] for res in results)
    percentage_successful = total_successful / len(results) if len(results) > 0 else 0.0

    print("Results:")
    print(f"  Successful files: {total_successful}")
    print(f"  Total files: {len(results)}")
    print(f"  Overall success rate: {100 * percentage_successful:.1f}%")

    # Debug: Show details about failures
    failed_count = len(results) - total_successful
    if failed_count > 0:
        print(f"\nFailed items: {failed_count}")
        for i, res in enumerate(results):
            if not res["success"]:
                print(f"  Item {i + 1}: Failed - check logs for details")
