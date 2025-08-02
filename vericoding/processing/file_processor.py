"""File processing logic."""

import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from ..core.config import ProcessingConfig
from ..core.llm_providers import create_llm_provider
from ..core.prompts import PromptLoader
from ..core.language_tools import verify_file
from ..utils.io_utils import thread_safe_print, save_iteration_code
from .code_fixer import extract_code, verify_spec_preservation, restore_specs


@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool
    file: str
    output: str | None
    error: str | None
    has_bypass: bool


def call_llm_api(config: ProcessingConfig, prompt: str) -> str:
    """Call LLM API with the given prompt using the configured provider."""
    # Add rate limiting delay to avoid overwhelming the API
    time.sleep(config.api_rate_limit_delay)

    # Create the LLM provider
    try:
        llm_provider = create_llm_provider(config.llm_provider, config.llm_model)
        return llm_provider.call_api(prompt)
    except Exception as e:
        raise ValueError(f"Error calling {config.llm_provider} API: {str(e)}")


def process_spec_file(
    config: ProcessingConfig, prompt_loader: PromptLoader, file_path: str
) -> ProcessingResult:
    """Process a single specification file."""
    try:
        thread_safe_print(f"Processing: {Path(file_path).name}")

        # Read the original file
        with Path(file_path).open() as f:
            original_code = f.read()

        # Calculate relative path from input directory to preserve hierarchy
        relative_path = Path(file_path).relative_to(Path(config.files_dir))
        base_file_name = Path(file_path).stem

        # Save original code
        save_iteration_code(config, relative_path, 0, original_code, "original")

        # Check if original file has compilation errors
        thread_safe_print("  Checking original file for compilation errors...")
        original_verification = verify_file(config, file_path)

        if not original_verification.success:
            thread_safe_print(
                f"  ⚠️  Original file has issues: {original_verification.error}"
            )
            thread_safe_print("  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications
        thread_safe_print("  Step 1: Generating code from specifications...")
        try:
            generate_prompt = prompt_loader.format_prompt(
                "generate_code", code=original_code
            )
        except KeyError as e:
            thread_safe_print(f"  ✗ Prompt error: {e}")
            thread_safe_print(
                f"  Available prompts: {list(prompt_loader.prompts.keys())}"
            )
            raise
        except Exception as e:
            thread_safe_print(f"  ✗ Error formatting prompt: {e}")
            raise

        generated_response = call_llm_api(config, generate_prompt)
        generated_code = extract_code(config, generated_response)

        # Verify that all specifications are preserved
        if config.strict_spec_verification and not verify_spec_preservation(
            config, original_code, generated_code
        ):
            thread_safe_print(
                "  ⚠️  Warning: Specifications were modified. Restoring original specifications..."
            )
            generated_code = restore_specs(config, original_code, generated_code)

        # Save initial generated code
        save_iteration_code(config, relative_path, 1, generated_code, "generated")

        # Create output file path preserving directory structure
        relative_dir = relative_path.parent
        output_subdir = (
            Path(config.output_dir) / relative_dir
            if str(relative_dir) != "."
            else Path(config.output_dir)
        )

        # Thread-safe directory creation
        from ..utils.io_utils import file_write_lock

        with file_write_lock():
            output_subdir.mkdir(parents=True, exist_ok=True)

        output_path = (
            output_subdir
            / f"{base_file_name}_impl{config.language_config.file_extension}"
        )
        with output_path.open("w") as f:
            f.write(generated_code)

        # Run verification iterations
        current_code = generated_code
        success = False
        last_verification = None

        for iteration in range(1, config.max_iterations + 1):
            thread_safe_print(
                f"  Iteration {iteration}/{config.max_iterations}: Verifying..."
            )

            # Write current code to file
            with output_path.open("w") as f:
                f.write(current_code)

            # Save current working version for this iteration
            save_iteration_code(
                config, relative_path, iteration, current_code, "current"
            )

            # Verify
            verification = verify_file(config, str(output_path))
            last_verification = verification

            if verification.success:
                thread_safe_print("    ✓ Verification successful!")
                success = True
                break
            else:
                thread_safe_print(
                    f"    ✗ Verification failed: {verification.error[:200] if verification.error else 'Unknown error'}..."
                )

            # Try to fix issues (both compilation and verification errors)
            error_details = verification.error or "Unknown error"

            # Only attempt fix if not on last iteration
            if iteration < config.max_iterations:
                thread_safe_print("    Attempting to fix errors...")
                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    errorDetails=error_details,
                    iteration=iteration,
                )

                try:
                    fix_response = call_llm_api(config, fix_prompt)
                    fixed_code = extract_code(config, fix_response)

                    # Verify that all specifications are still preserved
                    if config.strict_spec_verification and not verify_spec_preservation(
                        config, original_code, fixed_code
                    ):
                        thread_safe_print(
                            "    ⚠️  Warning: Specifications were modified during fix. Restoring original specifications..."
                        )
                        fixed_code = restore_specs(config, original_code, fixed_code)

                    current_code = fixed_code
                    thread_safe_print(f"    Generated fix for iteration {iteration}")
                except Exception as e:
                    thread_safe_print(f"    ✗ Failed to generate fix: {str(e)}")
                    break

        if success:
            thread_safe_print(
                f"  ✓ Successfully generated and verified: {output_path.name}"
            )
            return ProcessingResult(
                success=True,
                file=str(relative_path),
                output=str(output_path),
                error=None,
                has_bypass=False,
            )
        else:
            error_msg = (
                last_verification.error
                if last_verification
                else "Unknown verification error"
            )
            thread_safe_print(
                f"  ✗ Failed to verify after {config.max_iterations} iterations: {error_msg[:200] if error_msg else 'Unknown error'}..."
            )
            return ProcessingResult(
                success=False,
                file=str(relative_path),
                output=str(output_path),
                error=error_msg,
                has_bypass=False,
            )

    except Exception as e:
        thread_safe_print(f"✗ Failed: {Path(file_path).name} - {str(e)}")
        return ProcessingResult(
            success=False,
            file=str(relative_path)
            if "relative_path" in locals()
            else Path(file_path).name,
            error=str(e),
            output=None,
            has_bypass=False,
        )


def process_files_parallel(
    config: ProcessingConfig, prompt_loader: PromptLoader, spec_files: list[str]
) -> list[ProcessingResult]:
    """Process files in parallel using ThreadPoolExecutor."""
    results = []
    completed_count = 0
    total_files = len(spec_files)

    print(
        f"Processing {total_files} files using {config.max_workers} parallel workers..."
    )
    print("")

    with ThreadPoolExecutor(max_workers=config.max_workers) as executor:
        # Submit all tasks
        future_to_file = {
            executor.submit(
                process_spec_file, config, prompt_loader, file_path
            ): file_path
            for file_path in spec_files
        }

        # Process completed tasks as they finish
        for future in as_completed(future_to_file):
            file_path = future_to_file[future]
            completed_count += 1

            try:
                result = future.result()
                results.append(result)

                # Print progress update
                status = "✓" if result.success else "✗"
                thread_safe_print(
                    f"[{completed_count}/{total_files}] {status} {Path(file_path).name}"
                )

            except Exception as e:
                # Handle unexpected exceptions
                relative_path = Path(file_path).relative_to(Path(config.files_dir))
                error_result = ProcessingResult(
                    success=False,
                    file=str(relative_path),
                    error=f"Unexpected error: {str(e)}",
                    output=None,
                    has_bypass=False,
                )
                results.append(error_result)
                thread_safe_print(
                    f"[{completed_count}/{total_files}] ✗ {Path(file_path).name} - Unexpected error: {str(e)}"
                )

    return results
