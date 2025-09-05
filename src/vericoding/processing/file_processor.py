"""File processing logic."""

import logging
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from ..core.config import ProcessingConfig
from ..core.llm_providers import create_llm_provider
from ..core.prompts import PromptLoader
from ..core.language_tools import verify_file
from ..utils.io_utils import save_iteration_code
import wandb
import hashlib
from .code_fixer import extract_code, verify_spec_preservation, restore_specs
try:
    from ..lean.mcp_helpers import collect_lsp_context_safe  # optional
except Exception:
    def collect_lsp_context_safe(_file: str, _lines: list[int]) -> str:
        return ""

# Set up a basic logger
logging.basicConfig(level=logging.INFO, format="%(message)s")
logger = logging.getLogger(__name__)


@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool
    file: str
    output: str | None
    error: str | None
    has_bypass: bool
    generate_prompt: str | None = None
    fix_prompts: list[str] | None = None


def call_llm_api(config: ProcessingConfig, prompt: str) -> str:
    """Call LLM API with the given prompt using the configured provider."""
    # Add rate limiting delay to avoid overwhelming the API
    time.sleep(config.api_rate_limit_delay)

    # Create the LLM provider
    try:
        llm_provider = create_llm_provider(
            config.llm_provider,
            config.llm_model,
            reasoning_effort=getattr(config, "llm_reasoning_effort", None),
        )
        
        # Log LLM call start
        start_time = time.time()
        response = llm_provider.call_api(prompt)
        latency_ms = (time.time() - start_time) * 1000
        
        # Log to wandb if run is active
        if wandb.run:
            wandb.log({
                "llm/calls": 1,
                "llm/latency_ms": latency_ms,
                "llm/model": config.llm_model or config.llm_provider
            })
        
        return response
    except Exception as e:
        raise ValueError(f"Error calling {config.llm_provider} API: {str(e)}")


def process_spec_file(
    config: ProcessingConfig, prompt_loader: PromptLoader, file_path: str
) -> ProcessingResult:
    """Process a single specification file."""
    # Initialize failure tracking table if wandb is active
    failure_table = None
    mcp_context_table = None
    if wandb.run:
        failure_table = wandb.Table(columns=[
            "file", "iteration", "spec_hash", "code_hash",
            "error_msg", "proof_state", "timestamp"
        ])
        mcp_context_table = wandb.Table(columns=[
            "file", "stage", "iteration", "context_len", "context_preview"
        ])
    
    try:
        logger.info(f"Processing: {Path(file_path).name}")

        # Read the original file
        with Path(file_path).open() as f:
            original_code = f.read()

        # Calculate relative path from input directory to preserve hierarchy
        relative_path = Path(file_path).relative_to(Path(config.files_dir))
        base_file_name = Path(file_path).stem
        
        # Track prompts for W&B logging
        all_fix_prompts = []

        # Save original code
        save_iteration_code(config, relative_path, 0, original_code, "original")

        # Check if original file has compilation errors
        logger.info("  Checking original file for compilation errors...")
        original_verification = verify_file(config, file_path)

        if not original_verification.success:
            logger.info(f"  ⚠️  Original file has issues: {original_verification.error}")
            logger.info("  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications
        logger.info("  Step 1: Generating code from specifications...")
        try:
            lsp_context = ""
            if config.use_mcp and config.language == "lean":
                sorry_lines = [i + 1 for i, ln in enumerate(original_code.splitlines()) if "sorry" in ln]
                lsp_context = collect_lsp_context_safe(file_path, sorry_lines)
                if wandb.run and lsp_context:
                    wandb.log({"mcp/original_lsp_context_len": len(lsp_context)})
                    # Log skimmable context
                    preview = lsp_context[:2000]
                    mcp_context_table.add_data(
                        str(relative_path), "generate", 0, len(lsp_context), preview
                    )
                    # Quick tool usage signals for hover/goals
                    try:
                        hover_calls = lsp_context.count(" hover\n")
                        goal_calls = lsp_context.count(" goals\n")
                        wandb.log({
                            "mcp/hover_calls_generate": hover_calls,
                            "mcp/goal_calls_generate": goal_calls,
                        })
                    except Exception:
                        pass

            generate_prompt = prompt_loader.format_prompt(
                "generate_code", code=original_code, lspContext=lsp_context, errorDetails=""
            )
        except KeyError as e:
            logger.info(f"  ✗ Prompt error: {e}")
            logger.info(f"  Available prompts: {list(prompt_loader.prompts.keys())}")
            raise
        except Exception as e:
            logger.info(f"  ✗ Error formatting prompt: {e}")
            raise

        generated_response = call_llm_api(config, generate_prompt)
        generated_code = extract_code(config, generated_response)

        # Verify that all specifications are preserved
        if config.strict_spec_verification and not verify_spec_preservation(
            config, original_code, generated_code
        ):
            logger.info(
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
        logger.info(f"    💾 Writing output file: {output_path.resolve()}")
        with output_path.open("w") as f:
            f.write(generated_code)

        # Run verification iterations
        current_code = generated_code
        success = False
        last_verification = None

        for iteration in range(1, config.max_iterations + 1):
            logger.info(
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
            
            # Log verification attempt to wandb
            if wandb.run:
                file_key = Path(file_path).stem
                wandb.log({
                    f"verify/{file_key}/iter": iteration,
                    f"verify/{file_key}/success": int(verification.success)
                })
                
                # Log failure details to table
                if not verification.success and failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        iteration,
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        hashlib.md5(current_code.encode()).hexdigest()[:8],
                        verification.error if verification.error else "Unknown error",  # Full error message
                        "",  # Proof state would come from lean tools
                        time.time()
                    )

            if verification.success:
                logger.info("    ✓ Verification successful!")
                success = True
                break
            else:
                # Save full error log to debug directory
                if config.debug_mode and verification.error:
                    error_log_path = (
                        Path(config.output_dir) / "debug" / relative_path.parent
                        if str(relative_path.parent) != "."
                        else Path(config.output_dir) / "debug"
                    ) / f"{base_file_name}_iter{iteration}_error.log"
                    
                    error_log_path.parent.mkdir(parents=True, exist_ok=True)
                    with error_log_path.open("w") as f:
                        f.write(f"=== Verification Error - Iteration {iteration} ===\n")
                        f.write(f"File: {file_path}\n")
                        f.write(f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                        f.write(f"\nFull Error Output:\n")
                        f.write("-" * 80 + "\n")
                        f.write(verification.error)
                        f.write("\n" + "-" * 80 + "\n")
                        if verification.output:
                            f.write("\nAdditional Output:\n")
                            f.write(verification.output)
                    logger.info(f"    💾 Saved full error log to: {error_log_path.resolve()}")
                
                logger.info(
                    f"    ✗ Verification failed: {verification.error[:200] if verification.error else 'Unknown error'}..."
                )

            # Try to fix issues (both compilation and verification errors)
            error_details = verification.error or "Unknown error"

            # Only attempt fix if not on last iteration
            if iteration < config.max_iterations:
                logger.info("    Attempting to fix errors...")
                lsp_context = ""
                if config.use_mcp and config.language == "lean":
                    sorry_lines = [i + 1 for i, ln in enumerate(current_code.splitlines()) if "sorry" in ln]
                    lsp_context = collect_lsp_context_safe(str(output_path), sorry_lines)
                    if wandb.run and lsp_context:
                        wandb.log({"mcp/fix_lsp_context_len": len(lsp_context)})
                        preview = lsp_context[:2000]
                        mcp_context_table.add_data(
                            str(relative_path), "fix", iteration, len(lsp_context), preview
                        )
                        try:
                            hover_calls = lsp_context.count(" hover\n")
                            goal_calls = lsp_context.count(" goals\n")
                            wandb.log({
                                "mcp/hover_calls_fix": hover_calls,
                                "mcp/goal_calls_fix": goal_calls,
                                "mcp/fix_iteration": iteration,
                            })
                        except Exception:
                            pass

                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    errorDetails=error_details,
                    iteration=iteration,
                    lspContext=lsp_context,
                )

                # Track fix prompt for W&B logging
                all_fix_prompts.append(fix_prompt)
                
                try:
                    fix_response = call_llm_api(config, fix_prompt)
                    fixed_code = extract_code(config, fix_response)

                    # Verify that all specifications are still preserved
                    if config.strict_spec_verification and not verify_spec_preservation(
                        config, original_code, fixed_code
                    ):
                        logger.info(
                            "    ⚠️  Warning: Specifications were modified during fix. Restoring original specifications..."
                        )
                        fixed_code = restore_specs(config, original_code, fixed_code)

                    current_code = fixed_code
                    logger.info(f"    Generated fix for iteration {iteration}")
                    
                    # Fixed code will be saved in next iteration
                except Exception as e:
                    logger.info(f"    ✗ Failed to generate fix: {str(e)}")
                    break

        if success:
            logger.info(f"  ✓ Successfully generated and verified: {output_path.name}")
            
            # Track success in wandb
            if wandb.run:
                file_key = Path(file_path).stem
                wandb.log({
                    f"verify/{file_key}/final_iter": iteration,
                    f"verify/{file_key}/success": 1,
                    "success_count": 1
                })
            
            return ProcessingResult(
                success=True,
                file=str(relative_path),
                output=str(output_path),
                error=None,
                has_bypass=False,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
            )
        else:
            error_msg = (
                last_verification.error
                if last_verification
                else "Unknown verification error"
            )
            logger.info(
                f"  ✗ Failed to verify after {config.max_iterations} iterations: {error_msg[:200] if error_msg else 'Unknown error'}..."
            )
            
            # Track failure in wandb
            if wandb.run:
                file_key = Path(file_path).stem
                wandb.log({
                    f"verify/{file_key}/final_iter": config.max_iterations,
                    f"verify/{file_key}/success": 0,
                    "failure_count": 1
                })
                
                # Add final failure to table
                if failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        config.max_iterations,
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        hashlib.md5(current_code.encode() if 'current_code' in locals() else generated_code.encode()).hexdigest()[:8],
                        error_msg if error_msg else "Unknown error",  # Full error message
                        "",
                        time.time()
                    )
            
            return ProcessingResult(
                success=False,
                file=str(relative_path),
                output=str(output_path),
                error=error_msg,
                has_bypass=False,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
            )

    except Exception as e:
        logger.info(f"✗ Failed: {Path(file_path).name} - {str(e)}")
        
        # Track exception in wandb
        if wandb.run:
            file_key = Path(file_path).stem
            wandb.log({
                f"verify/{file_key}/exception": 1,
                "exception_count": 1
            })
        
        return ProcessingResult(
            success=False,
            file=str(relative_path)
            if "relative_path" in locals()
            else Path(file_path).name,
            error=str(e),
            output=None,
            has_bypass=False,
            generate_prompt=generate_prompt if "generate_prompt" in locals() else None,
            fix_prompts=all_fix_prompts if "all_fix_prompts" in locals() and all_fix_prompts else None,
        )
    finally:
        # Log failure table if we have any failures
        if wandb.run:
            if failure_table is not None and len(failure_table.data) > 0:
                wandb.log({"verification_failures": failure_table})
            if mcp_context_table is not None and len(mcp_context_table.data) > 0:
                wandb.log({"mcp_contexts": mcp_context_table})


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
                logger.info(
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
                    generate_prompt=None,
                    fix_prompts=None,
                )
                results.append(error_result)
                logger.info(
                    f"[{completed_count}/{total_files}] ✗ {Path(file_path).name} - Unexpected error: {str(e)}"
                )

    return results
