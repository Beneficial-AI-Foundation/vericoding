"""Item processing and async logic for code2verus"""

import asyncio
import random
from pathlib import Path
from pydantic_ai import ModelHTTPError
import logfire
import yaml

from code2verus.config import ARTIFACTS, get_config_value
from code2verus.agent import translate_code_to_verus
from code2verus.verification import verify_code
from code2verus.success_tracker import save_success_info, is_sample_already_successful
from code2verus.debug_utils import save_debug_context, generate_debug_report
from code2verus.models import TranslationDebugContext


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
    target_language: str = "verus",
    benchmark_name: str = "dafnybench",
    max_retries: int | None = None,
    base_delay: float = 5.0,
    is_flat: bool = False,
    is_yaml: bool = False,
    benchmark_path: str = "",
    # Debug options
    save_debug: bool = False,
    debug_dir: Path = Path("debug_sessions"),
    debug_report: bool = False,
    include_debug_in_result: bool = False,
) -> dict:
    """Process a single item from the dataset with exponential backoff"""

    # Use config value if max_retries not provided
    if max_retries is None:
        max_retries = get_config_value("max_retries")

    # Type assertion to help type checker
    assert isinstance(max_retries, int)

    # Determine file suffix based on target language
    if is_yaml:
        suffix = ".yaml"
    elif target_language == "verus":
        suffix = ".rs"
    elif target_language == "dafny":
        suffix = ".dfy"
    elif target_language == "lean":
        suffix = ".lean"
    else:
        suffix = ".txt"  # fallback

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

    # Log input file path if available
    if "source_path" in item:
        logfire.info(f"Input file path: {item['source_path']}")
    elif "test_file" in item:
        # For benchmarks that use test_file, construct the full path
        full_input_path = Path(benchmark_path) / item["test_file"]
        logfire.info(f"Input file path: {full_input_path}")
    else:
        logfire.info(f"Input file: {source_filename} (generated filename)")

    artifact_path.mkdir(parents=True, exist_ok=True)

    # Exponential backoff retry logic
    for attempt in range(max_retries + 1):
        try:
            translation_result = await translate_code_to_verus(
                source_code, source_language, target_language, is_yaml
            )

            translated_code = translation_result.output_content
            num_iterations = translation_result.num_iterations
            code_for_verification = translation_result.code_for_verification
            debug_context = translation_result.debug_context

            logfire.info(f"Translation took {num_iterations} iterations")

            # Handle debug options
            if debug_context:
                # Save debug context if requested
                if save_debug:
                    try:
                        debug_path = save_debug_context(debug_context, debug_dir)
                        logfire.info(f"Debug context saved to: {debug_path}")
                    except Exception as e:
                        logfire.warning(f"Failed to save debug context: {e}")

                # Generate debug report if requested
                if debug_report:
                    try:
                        report = generate_debug_report(debug_context)
                        print(f"\n=== Debug Report for Item {idx} ===")
                        print(report)
                        print("=" * 50)
                    except Exception as e:
                        logfire.warning(f"Failed to generate debug report: {e}")

                # Log debug summary
                summary = debug_context.to_summary_dict()
                logfire.info(f"Translation debug summary for item {idx}", extra=summary)

            # Do a final verification to get the verification status for reporting
            # (the agent already did verification during iterations, but we need the final status)
            (
                verification_success,
                verification_output,
                verification_error,
            ) = await verify_code(
                code_for_verification,
                target_language,
                is_yaml,
                output_filename,
                benchmark_name,
                benchmark_path,
            )

            # Determine subfolder based on compilation success
            compilation_status = (
                "compiling" if verification_success else "non_compiling"
            )

            # Save the main output (YAML for YAML files, target language files for regular files) in appropriate subfolder
            status_artifact_path = artifact_path / compilation_status
            status_artifact_path.mkdir(parents=True, exist_ok=True)
            output_file_path = status_artifact_path / output_filename
            with open(output_file_path, "w") as output_file:
                output_file.write(translated_code)
            logfire.info(
                f"Generated {target_language} code saved to: {output_file_path}"
            )

            # Update debug context with output file path if available
            if debug_context:
                debug_context.set_output_file_path(str(output_file_path))

            # For YAML files, also save the target language code in the files folder for verification
            if is_yaml:
                # Create the files folder equivalent path with compilation status
                files_path = derive_output_path(
                    benchmark_path, benchmark_name, is_yaml=False
                )
                code_status_path = (
                    files_path / relative_path.parent / compilation_status
                )
                code_output_path = (
                    code_status_path / Path(output_filename).with_suffix(".rs").name
                )
                code_output_path.parent.mkdir(parents=True, exist_ok=True)

                with open(code_output_path, "w") as code_file:
                    code_file.write(code_for_verification)
                logfire.info(
                    f"Generated code for verification saved to: {code_output_path}"
                )

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

            result = {"path": artifact_path, "success": verification_success}

            # Include debug context in result if requested
            if include_debug_in_result and debug_context:
                result["debug_context"] = debug_context

            return result

        except ModelHTTPError as exc:
            if attempt == max_retries:
                logfire.info(
                    f"Failed to process item {idx + 1} after {max_retries} retries: {exc}"
                )
                raise

            # Calculate delay with exponential backoff and jitter
            delay = base_delay * (2**attempt) + random.uniform(0, 1)
            logfire.info(
                f"Rate limited on item {idx + 1}, file {source_filename}, attempt {attempt + 1}/{max_retries + 1}. Retrying in {delay:.2f}s..."
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
    target_language: str = "verus",
    max_concurrent: int = 3,
    file_pattern: str = "*.dfy",
    limit: int | None = None,
    # Debug options
    save_debug: bool = False,
    debug_dir: Path = Path("debug_sessions"),
    debug_report: bool = False,
    debug_summary: bool = False,
    include_debug_in_result: bool = False,
) -> None:
    """Async main function for parallel processing with debug support"""
    from code2verus.benchmarks import load_benchmark, is_flat_structure

    print("Code2Verus translator initialized!")

    # Load the dataset
    dataset = load_benchmark(benchmark, split, file_pattern)

    # Apply limit if specified
    if limit is not None and limit > 0:
        # Convert dataset to list for uniform handling
        if isinstance(dataset, list):
            dataset_list: list | None = dataset
        else:
            # Handle Hugging Face datasets and other iterable types
            try:
                dataset_list = list(dataset)
            except Exception as e:
                logfire.warning(f"Could not convert dataset to list: {e}")
                # If conversion fails, skip limiting and use original dataset
                dataset_list = None

        if dataset_list is not None:
            original_length = len(dataset_list)

            if limit >= original_length:
                print(
                    f"Limit ({limit}) is greater than or equal to available files ({original_length}), processing all files"
                )
                dataset = dataset_list
            else:
                dataset = dataset_list[:limit]
                print(f"Limited dataset from {original_length} to {len(dataset)} files")
        else:
            print("Could not apply limit - using original dataset")

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
        check_existing_success(
            idx, item, benchmark_name, is_flat=is_flat, benchmark_path=benchmark
        )
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
                target_language,
                benchmark_name,
                base_delay=5.0,
                is_flat=is_flat,
                is_yaml=is_yaml,
                benchmark_path=benchmark,
                # Debug options
                save_debug=save_debug,
                debug_dir=debug_dir,
                debug_report=debug_report,
                include_debug_in_result=include_debug_in_result,
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
    percentage_successful = total_successful / max(len(results), 1)

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

    # Generate debug summary if requested
    if debug_summary and include_debug_in_result:
        print("\n" + "=" * 60)
        print("DEBUG SUMMARY")
        print("=" * 60)

        debug_contexts: list[TranslationDebugContext] = [
            res["debug_context"]
            for res in results
            if res.get("debug_context") is not None
        ]

        if debug_contexts:
            # Aggregate statistics
            total_iterations = sum(ctx.current_iteration for ctx in debug_contexts)
            total_errors = sum(len(ctx.verification_errors) for ctx in debug_contexts)
            total_exchanges = sum(
                len(ctx.conversation_exchanges) for ctx in debug_contexts
            )

            successful_contexts = [
                ctx for ctx in debug_contexts if ctx.get_final_status() == "success"
            ]
            failed_contexts = [
                ctx for ctx in debug_contexts if ctx.get_final_status() != "success"
            ]

            print(f"Total debug contexts: {len(debug_contexts)}")
            print(f"Successful translations: {len(successful_contexts)}")
            print(f"Failed translations: {len(failed_contexts)}")
            print(f"Total iterations across all translations: {total_iterations}")
            print(
                f"Average iterations per translation: {total_iterations / len(debug_contexts):.2f}"
            )
            print(f"Total verification errors: {total_errors}")
            print(f"Total conversation exchanges: {total_exchanges}")

            # Error pattern analysis
            if total_errors > 0:
                error_types = {}
                for ctx in debug_contexts:
                    for error in ctx.verification_errors:
                        error_types[error.error_type] = (
                            error_types.get(error.error_type, 0) + 1
                        )

                print("\nError type breakdown:")
                for error_type, count in sorted(
                    error_types.items(), key=lambda x: x[1], reverse=True
                ):
                    print(
                        f"  {error_type}: {count} ({count / total_errors * 100:.1f}%)"
                    )

            # Performance insights
            if successful_contexts:
                avg_successful_iterations = sum(
                    ctx.current_iteration for ctx in successful_contexts
                ) / len(successful_contexts)
                print(
                    f"\nSuccessful translations averaged {avg_successful_iterations:.2f} iterations"
                )

            if failed_contexts:
                avg_failed_iterations = sum(
                    ctx.current_iteration for ctx in failed_contexts
                ) / len(failed_contexts)
                print(
                    f"Failed translations averaged {avg_failed_iterations:.2f} iterations"
                )

                # Most common failure reasons
                failure_reasons = {}
                for ctx in failed_contexts:
                    status = ctx.get_final_status()
                    failure_reasons[status] = failure_reasons.get(status, 0) + 1

                print("\nFailure reasons:")
                for reason, count in sorted(
                    failure_reasons.items(), key=lambda x: x[1], reverse=True
                ):
                    print(
                        f"  {reason}: {count} ({count / len(failed_contexts) * 100:.1f}%)"
                    )
        else:
            print(
                "No debug contexts available (use --include-debug-in-result to collect them)"
            )

        print("=" * 60)
    elif debug_summary and not include_debug_in_result:
        print("\n⚠️  Debug summary requested but --include-debug-in-result not set.")
        print(
            "   Use --include-debug-in-result to collect debug contexts for summary analysis."
        )
