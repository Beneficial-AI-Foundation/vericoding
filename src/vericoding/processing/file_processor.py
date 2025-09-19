"""File processing logic."""

import hashlib
import logging
import re
import time
import traceback
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from pathlib import Path

import wandb

from ..core.config import ProcessingConfig
from ..core.llm_providers import create_llm_provider
from ..core.prompts import PromptLoader
from ..core.language_tools import verify_file
from ..core.llm_providers import call_llm
from ..utils.io_utils import save_iteration_code, load_postamble_from_yaml
from .code_fixer import extract_code, apply_json_replacements
from .cheat_checker import has_final_failure_cheats, check_for_cheats

# Import for Lean preprocessing
from ..preprocessing import preprocess_lean_file, ensure_mathlib_import


def count_placeholders(original_code: str, language: str) -> int:
    """Count placeholders in original code for JSON array sizing.
    
    Args:
        original_code: The original code content
        language: The programming language ("lean", "dafny", "verus")
        
    Returns:
        Number of placeholders that need to be replaced
        
    Raises:
        ValueError: If unsupported language is provided
    """
    if language == "lean":
        # Count sorries only inside editable sections (vc-definitions, vc-theorems, vc-helpers)
        editable_sections = []
        for section_name in ['vc-definitions', 'vc-theorems', 'vc-helpers']:
            pattern = rf'<{section_name}>(.*?)</{section_name}>'
            matches = list(re.finditer(pattern, original_code, re.DOTALL))
            editable_sections.extend([(match.start(), match.end()) for match in matches])

        sorry_count = 0
        search_start = 0
        while True:
            pos = original_code.find("sorry", search_start)
            if pos == -1:
                break
            # Only count if inside an editable section
            in_editable_section = any(start <= pos < end for start, end in editable_sections)
            if in_editable_section:
                sorry_count += 1
            search_start = pos + 1

        # Also count vc-helpers sections themselves (they can be replaced with helper content)
        placeholder_count = sorry_count + original_code.count("<vc-helpers>")
    elif language in ("dafny", "verus"):
        placeholder_count = original_code.count("<vc-code>") + original_code.count("<vc-helpers>")
    else:
        raise ValueError(f"Unsupported language: {language}. Supported languages are: lean, dafny, verus")
    
    return placeholder_count


# Set up a basic logger
logging.basicConfig(level=logging.INFO, format="%(message)s")
logger = logging.getLogger(__name__)


@dataclass
class LLMResponse:
    """Individual LLM response data."""
    file: str
    response_type: str  # "generate_code" or "fix_verification"
    iteration: int
    prompt_hash: str
    response_content: str
    json_parsed_successfully: bool
    timestamp: float

@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool
    file: str
    output: str | None
    error: str | None
    has_bypass: bool
    original_compilation_failed: bool = False
    generate_prompt: str | None = None
    fix_prompts: list[str] | None = None
    llm_responses: list[LLMResponse] | None = None


@dataclass 
class UnitTestResult:
    """Result of unit test with postamble."""
    success: bool
    verification: 'VerificationResult'




def run_unit_test_with_postamble(
    config: ProcessingConfig, 
    current_code: str, 
    file_path: str, 
    relative_path: Path, 
    output_path: Path, 
    base_file_name: str, 
    iteration: int
) -> UnitTestResult:
    """Run unit test with postamble for Lean files.
    
    This function is only called when verification succeeded and no cheats were found.
    
    Args:
        config: Processing configuration
        current_code: The current working code (clean, no cheats)
        file_path: Path to the original file
        relative_path: Relative path from files_dir  
        output_path: Path to the output file
        base_file_name: Base filename without extension
        iteration: Current iteration number
        
    Returns:
        UnitTestResult with success status and verification result
    """
    logger.info("    🧪 Testing with postamble...")
    
    # Load postamble from YAML
    relative_path_for_yaml = Path(file_path).relative_to(Path(config.files_dir))
    postamble = load_postamble_from_yaml(config, relative_path_for_yaml)
    
    if not postamble:
        logger.info("    ⚠️  No postamble found - treating as normal success")
        from ..core.language_tools import VerificationResult
        verification = VerificationResult(success=True, error=None, output="")
        return UnitTestResult(success=True, verification=verification)
    
    # Create code with postamble appended
    code_with_postamble = current_code + "\n\n" + postamble
    
    # Save code with postamble for debugging
    save_iteration_code(config, relative_path, iteration, code_with_postamble, "unit_test_with_postamble")
    
    # Write code with postamble to temporary file for verification
    temp_output_path = output_path.with_suffix(".unit_test" + config.language_config.file_extension)
    with temp_output_path.open("w") as f:
        f.write(code_with_postamble)
    
    # Verify with postamble
    logger.info("    🧪 Verifying with postamble...")
    postamble_verification = verify_file(config, str(temp_output_path))
    
    if postamble_verification.success:
        logger.info("    ✓ Unit test PASSED: Verification with postamble successful!")
        
        # Clean up temporary file
        temp_output_path.unlink()
        return UnitTestResult(success=True, verification=postamble_verification)
    else:
        logger.info(f"    ✗ Unit test FAILED: Verification with postamble failed")
        logger.info(f"    ✗ Postamble error: {postamble_verification.error[:200] if postamble_verification.error else 'Unknown error'}...")
        
        # Update verification result to reflect unit test failure
        postamble_error = postamble_verification.error or "Unknown postamble verification error"
        combined_error = f"UNIT TEST FAILED: Solution passed verification but failed when postamble was added.\n\nPostamble verification error:\n{postamble_error}"
        
        # Save postamble error for debugging
        if config.debug_mode:
            postamble_error_log_path = (
                Path(config.output_dir) / "debug" / relative_path.parent
                if str(relative_path.parent) != "."
                else Path(config.output_dir) / "debug"
            ) / f"{base_file_name}_iter{iteration}_unit_test_postamble_error.log"
            
            postamble_error_log_path.parent.mkdir(parents=True, exist_ok=True)
            with postamble_error_log_path.open("w") as f:
                f.write(f"=== Unit Test Postamble Error - Iteration {iteration} ===\n")
                f.write(f"File: {file_path}\n")
                f.write(f"Time: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"\nPostamble Verification Error:\n")
                f.write("-" * 80 + "\n")
                f.write(postamble_error)
                f.write("\n" + "-" * 80 + "\n")
                f.write("\nPostamble Content:\n")
                f.write("-" * 80 + "\n")
                f.write(postamble)
                f.write("\n" + "-" * 80 + "\n")
            logger.info(f"    💾 Saved postamble error log to: debug/{relative_path.parent}/{base_file_name}_iter{iteration}_unit_test_postamble_error.log")
        
        # Clean up temporary file
        if temp_output_path.exists():
            temp_output_path.unlink()
        
        # Create failure verification result
        from ..core.language_tools import VerificationResult
        verification = VerificationResult(success=False, error=combined_error, output=postamble_verification.output)
        return UnitTestResult(success=False, verification=verification)


def process_spec_file(
    config: ProcessingConfig, prompt_loader: PromptLoader, file_path: str
) -> ProcessingResult:
    """Process a single specification file."""
    # Initialize tracking tables and response collection
    failure_table = None
    llm_responses = []
    if wandb.run:
        failure_table = wandb.Table(columns=[
            "file", "iteration", "spec_hash", "code_hash",
            "error_msg", "proof_state", "timestamp"
        ])
    
    try:
        logger.info(f"Processing: {Path(file_path).name}")

        # Read the original file
        with Path(file_path).open() as f:
            original_code = f.read()
        
        # Apply mandatory Lean preprocessing (Mathlib import)
        if config.language == "lean":
            original_code = ensure_mathlib_import(original_code)
        
        # Apply optional Lean preprocessing (sorry wrapping) if assume-unformatted-lean is enabled
        if (config.language == "lean" and config.assume_unformatted_lean):
            original_code = preprocess_lean_file(original_code)

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
        original_compilation_failed = not original_verification.success

        if original_compilation_failed:
            logger.info(f"  ⚠️  Original file has issues: {original_verification.error}")
            logger.info("  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications
        logger.info("  Step 1: Generating code from specifications...")
        try:
            # Count placeholders in original code for JSON array sizing
            placeholder_count = count_placeholders(original_code, config.language)
            
            generate_prompt = prompt_loader.format_prompt(
                "generate_code", 
                code=original_code, 
                placeholder_count=placeholder_count,
                max_iterations=config.max_iterations
            )
        except KeyError as e:
            logger.info(f"  ✗ Prompt error: {e}")
            logger.info(f"  Available prompts: {list(prompt_loader.prompts.keys())}")
            raise
        except Exception as e:
            logger.info(f"  ✗ Error formatting prompt: {e}")
            raise

        # Create LLM provider for this request
        llm_provider, _ = create_llm_provider(config.llm)
        generated_response = call_llm(llm_provider, config, generate_prompt, wandb)
        
        # IMMEDIATELY save raw response to debug folder before any parsing
        if config.debug_mode:
            relative_path = Path(file_path).relative_to(Path(config.files_dir))
            base_file_name = Path(file_path).stem
            debug_dir = (
                Path(config.output_dir) / "debug" / relative_path.parent
                if str(relative_path.parent) != "."
                else Path(config.output_dir) / "debug"
            )
            debug_dir.mkdir(parents=True, exist_ok=True)
            
            raw_response_file = debug_dir / f"{base_file_name}_raw_generate_response.txt"
            with raw_response_file.open("w") as f:
                f.write(f"=== Raw LLM Generate Response ===\n")
                f.write(f"Length: {len(generated_response)} characters\n")
                f.write("-" * 80 + "\n")
                f.write(generated_response)
                f.write("\n" + "-" * 80 + "\n")
        
        # Apply JSON replacements to original code (new approach)
        try:
            generated_code, json_error = apply_json_replacements(config, original_code, generated_response)
        except Exception as e:
            error_msg = f"Failed to apply JSON replacements: {str(e)}\n\nFull traceback:\n{traceback.format_exc()}"
            logger.error(error_msg)
            raise RuntimeError(error_msg) from e
        
        # If JSON parsing failed, try once more with a fresh LLM call
        if json_error and "JSON parsing failed" in json_error:
            logger.info(f"  ⚠️  JSON parsing failed, attempting retry...")
            try:
                retry_response = call_llm(llm_provider, config, generate_prompt, wandb)
                generated_code, json_error = apply_json_replacements(config, original_code, retry_response)
                
                if not json_error:
                    logger.info(f"  ✓ Retry successful - JSON parsed correctly")
                    # Update the response for logging
                    generated_response = retry_response
                else:
                    logger.info(f"  ✗ Retry also failed: {json_error}")
            except Exception as e:
                logger.error(f"  ✗ Retry attempt failed with error: {str(e)}")
                # Keep original error
        
        # Collect LLM response data
        if wandb.run:
            llm_responses.append(LLMResponse(
                file=file_path,
                response_type="generate_code",
                iteration=0,  # iteration 0 for initial generation
                prompt_hash=hashlib.md5(generate_prompt.encode()).hexdigest()[:8],
                response_content=generated_response,
                json_parsed_successfully=json_error is None,
                timestamp=time.time()
            ))
        
        # If JSON parsing failed, treat it as a verification failure
        if json_error:
            logger.info(f"  ✗ {json_error}")
            
            # Log JSON parsing failure to wandb like a verification failure
            if wandb.run:
                file_key = Path(file_path).stem
                wandb.log({
                    f"json_error/{file_key}/failed": 1,
                    f"verify/{file_key}/success": 0  # Count as verification failure
                })
                
                if failure_table is not None:
                    failure_table.add_data(
                        file_path,
                        0,  # iteration 0 for JSON parsing failures
                        hashlib.md5(original_code.encode()).hexdigest()[:8],
                        "",  # no generated code hash since parsing failed
                        json_error,
                        "",  # no proof state for JSON errors
                        time.time()
                    )
                
            return ProcessingResult(
                success=False,
                file=file_path,
                output=None,
                error=json_error,
                has_bypass=False,
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=[],
                llm_responses=llm_responses if wandb.run and llm_responses else None
            )
        
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
            
            # Check for cheats in final code - combine with verification output
            if has_final_failure_cheats(current_code, config.language):
                cheats = check_for_cheats(current_code, config.language)
                cheat_descriptions = [desc for _, desc in cheats]
                logger.info(f"    ⚠️ Final code contains verification bypasses: {'; '.join(cheat_descriptions)}")
                
                # Combine cheat message with original verification result
                cheat_message = f"VERIFICATION BYPASSES DETECTED: {'; '.join(cheat_descriptions)}. Code contains verification bypasses and cannot be considered successfully verified."
                
                if verification.success:
                    # Verification succeeded but cheats found
                    combined_error = f"{cheat_message}\n\nNote: Verification succeeded but verification bypasses prevent final success."
                    logger.info("    ✗ Marking as failed due to verification bypasses (verification succeeded)")
                else:
                    # Verification failed AND cheats found - combine both messages
                    original_error = verification.error or "Verification failed"
                    combined_error = f"{cheat_message}\n\nOriginal verification output:\n{original_error}"
                    logger.info("    ✗ Failed due to both verification errors AND verification bypasses")
                
                verification = replace(verification,
                    success=False,
                    error=combined_error
                )
            
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
                
                # Unit test mode: Test with postamble if enabled and code is clean (no cheats)
                if config.unit_test and config.language == 'lean' and not has_final_failure_cheats(current_code, config.language):
                    logger.info("    🧪 Clean solution found - entering unit test mode with postamble!")
                    unit_test_result = run_unit_test_with_postamble(
                        config, current_code, file_path, relative_path, 
                        output_path, base_file_name, iteration
                    )
                    success = unit_test_result.success
                    if not success:
                        verification = unit_test_result.verification
                        # In unit test mode, failure here is final - no more attempts
                        break
                else:
                    success = True
                
                if success:
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
                    logger.info(f"    💾 Saved full error log to: debug/{relative_path.parent}/{base_file_name}_iter{iteration}_error.log")
                
                logger.info(
                    f"    ✗ Verification failed: {verification.error[:200] if verification.error else 'Unknown error'}..."
                )

            # Try to fix issues (both compilation and verification errors)
            error_details = verification.error or "Unknown error"
            

            # Only attempt fix if not on last iteration
            if iteration < config.max_iterations:
                logger.info("    Attempting to fix errors...")
                # Count placeholders in original code for JSON array sizing (not current code!)
                placeholder_count = count_placeholders(original_code, config.language)
                
                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    original_code=original_code,
                    errorDetails=error_details,
                    iteration=iteration+1,
                    placeholder_count=placeholder_count,
                    max_iterations=config.max_iterations
                )

                # Track fix prompt for W&B logging
                all_fix_prompts.append(fix_prompt)
                
                try:
                    # Create LLM provider for fix request  
                    llm_provider, _ = create_llm_provider(config.llm)
                    fix_response = call_llm(llm_provider, config, fix_prompt, wandb)
                    
                    # IMMEDIATELY save raw response to debug folder before any parsing
                    if config.debug_mode:
                        relative_path = Path(file_path).relative_to(Path(config.files_dir))
                        base_file_name = Path(file_path).stem
                        debug_dir = (
                            Path(config.output_dir) / "debug" / relative_path.parent
                            if str(relative_path.parent) != "."
                            else Path(config.output_dir) / "debug"
                        )
                        debug_dir.mkdir(parents=True, exist_ok=True)
                        
                        raw_response_file = debug_dir / f"{base_file_name}_raw_fix_response_iter{iteration}.txt"
                        with raw_response_file.open("w") as f:
                            f.write(f"=== Raw LLM Fix Response - Iteration {iteration} ===\n")
                            f.write(f"Length: {len(fix_response)} characters\n")
                            f.write("-" * 80 + "\n")
                            f.write(fix_response)
                            f.write("\n" + "-" * 80 + "\n")
                    
                    # Apply JSON replacements for fix to the ORIGINAL file (which has placeholders)
                    # This ensures we're replacing sorry/vc-code tags, not broken implementations
                    try:
                        fixed_code, fix_json_error = apply_json_replacements(config, original_code, fix_response)
                    except Exception as e:
                        error_msg = f"Failed to apply JSON replacements: {str(e)}\n\nFull traceback:\n{traceback.format_exc()}"
                        logger.error(error_msg)
                        raise RuntimeError(error_msg) from e
                    
                    # Collect LLM fix response data
                    if wandb.run:
                        llm_responses.append(LLMResponse(
                            file=file_path,
                            response_type="fix_verification",
                            iteration=iteration,
                            prompt_hash=hashlib.md5(fix_prompt.encode()).hexdigest()[:8],
                            response_content=fix_response,
                            json_parsed_successfully=fix_json_error is None,
                            timestamp=time.time()
                        ))
                    
                    # If JSON parsing failed during fix, treat as iteration failure
                    if fix_json_error:
                        logger.info(f"    ✗ Fix JSON parsing failed: {fix_json_error}")
                        
                        # Log fix parsing failure to wandb
                        if wandb.run and failure_table is not None:
                            failure_table.add_data(
                                file_path,
                                iteration,
                                hashlib.md5(original_code.encode()).hexdigest()[:8],
                                hashlib.md5(current_code.encode()).hexdigest()[:8],
                                f"Fix JSON parsing failed: {fix_json_error}",
                                "",
                                time.time()
                            )
                        continue  # Skip to next iteration
                    
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
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
                llm_responses=llm_responses if wandb.run and llm_responses else None
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
                original_compilation_failed=original_compilation_failed,
                generate_prompt=generate_prompt,
                fix_prompts=all_fix_prompts if all_fix_prompts else None,
                llm_responses=llm_responses if wandb.run and llm_responses else None
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
            original_compilation_failed="original_compilation_failed" in locals() and original_compilation_failed,
            generate_prompt=generate_prompt if "generate_prompt" in locals() else None,
            fix_prompts=all_fix_prompts if "all_fix_prompts" in locals() and all_fix_prompts else None,
            llm_responses=llm_responses if wandb.run and "llm_responses" in locals() and llm_responses else None
        )
    finally:
        # Log failure table to W&B and save LLM responses to debug folder
        if wandb.run:
            if failure_table is not None and len(failure_table.data) > 0:
                wandb.log({"verification_failures": failure_table})
                
            # Save LLM responses to debug folder
            if config.debug_mode and llm_responses:
                relative_path = Path(file_path).relative_to(Path(config.files_dir))
                base_file_name = Path(file_path).stem
                debug_dir = (
                    Path(config.output_dir) / "debug" / relative_path.parent
                    if str(relative_path.parent) != "."
                    else Path(config.output_dir) / "debug"
                )
                debug_dir.mkdir(parents=True, exist_ok=True)
                
                for i, response in enumerate(llm_responses):
                    response_file = debug_dir / f"{base_file_name}_llm_response_{response.response_type}_iter{response.iteration}.txt"
                    with response_file.open("w") as f:
                        f.write(f"=== LLM Response - {response.response_type} - Iteration {response.iteration} ===\n")
                        f.write(f"File: {response.file}\n")
                        f.write(f"Prompt Hash: {response.prompt_hash}\n")
                        f.write(f"JSON Parsed Successfully: {response.json_parsed_successfully}\n")
                        f.write(f"Timestamp: {response.timestamp}\n")
                        f.write(f"Content Length: {len(response.response_content)} chars\n")
                        f.write("-" * 80 + "\n")
                        f.write(response.response_content)
                        f.write("\n" + "-" * 80 + "\n")


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
                    original_compilation_failed=False,  # Unknown since we didn't get that far
                    generate_prompt=None,
                    fix_prompts=None,
                )
                results.append(error_result)
                logger.info(
                    f"[{completed_count}/{total_files}] ✗ {Path(file_path).name} - Unexpected error: {str(e)}"
                )

    # Create consolidated LLM responses table
    if wandb.run:
        all_llm_responses = []
        for result in results:
            if result.llm_responses:
                all_llm_responses.extend(result.llm_responses)
        
        if all_llm_responses:
            llm_responses_table = wandb.Table(columns=[
                "file", "response_type", "iteration", "prompt_hash", 
                "response_content", "json_parsed_successfully", "timestamp"
            ])
            
            for response in all_llm_responses:
                llm_responses_table.add_data(
                    response.file,
                    response.response_type,
                    response.iteration,
                    response.prompt_hash,
                    response.response_content,
                    response.json_parsed_successfully,
                    response.timestamp
                )
            
            wandb.log({"llm_responses": llm_responses_table})
            logger.info(f"  📊 Logged {len(all_llm_responses)} LLM responses to W&B table")

    return results
