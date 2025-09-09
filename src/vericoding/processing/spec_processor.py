
import logging
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
import threading

from vericoding.core.config import ProcessingConfig
from vericoding.core.llm_providers import call_llm
from vericoding.core.prompts import PromptLoader
from vericoding.core.language_tools import verify_file
from vericoding.utils.io_utils import prepare_output_paths, save_iteration_code
from vericoding.processing.yaml_processor import (
    load_yaml,
    yaml_to_code,
    extract_sections,
    update_sections,
)
from vericoding.utils import wandb_utils

logger = logging.getLogger(__name__)


def validate_sections(vc_helpers: str, vc_spec: str, vc_code: str, vc_theorem: str = "", vc_proof: str = "", language: str = None, spec_mode: bool = True) -> Optional[str]:
    """Validate the extracted sections from LLM response.
    
    Args:
        vc_helpers: The helpers section content
        vc_spec: The spec section content  
        vc_code: The code section content
        vc_theorem: The theorem section content (for Lean)
        vc_proof: The proof section content (for Lean)
        language: The target language for language-specific validation
        spec_mode: Whether we're in spec mode (allows sorry in theorem sections)
        
    Returns:
        Error message if validation fails, None if valid
    """
    # Check for empty code
    if not vc_code or not vc_code.strip():
        return "Generated code is empty"
    
    sections_to_check = [
        ("vc-helpers", vc_helpers),
        ("vc-spec", vc_spec),
        ("vc-code", vc_code)
    ]
    
    # Add Lean-specific sections if present
    if language == "lean":
        if vc_theorem:
            sections_to_check.append(("vc-theorem", vc_theorem))
        if vc_proof:
            sections_to_check.append(("vc-proof", vc_proof))
    
    for section_name, content in sections_to_check:
        if not content:
            continue
            
        # Dafny/Verus-specific validation
        if language in ["dafny", "verus"]:
            # Check for assume statements (case insensitive, whole word)
            if re.search(r'\bassume\b', content, re.IGNORECASE):
                return f"Generated {section_name} contains 'assume' statements, which are not allowed"
            
            # Check for axiom attributes (case insensitive)
            if re.search(r'\{:axiom\}', content, re.IGNORECASE):
                return f"Generated {section_name} contains '{{:axiom}}' attributes, which are not allowed"
            
            # Check for method declarations in vc-code (should only contain method body)
            if section_name == "vc-code":
                if re.search(r'\bmethod\s+\w+', content, re.IGNORECASE):
                    return f"Generated {section_name} contains method declarations, only method body implementation is allowed"
    
    # Language-specific validation
    if language == "lean":
        return _validate_lean_sections(vc_helpers, vc_spec, vc_code, vc_theorem, vc_proof, spec_mode)
    
    return None


def _validate_lean_sections(vc_helpers: str, vc_spec: str, vc_code: str, vc_theorem: str, vc_proof: str, spec_mode: bool = True) -> Optional[str]:
    """Validate Lean-specific sections for verification bypasses and cheating.
    
    Args:
        spec_mode: If True, allows sorry in theorem sections (they are templates)
    
    Returns:
        Error message if validation fails, None if valid
    """
    # Combine all sections for comprehensive checking
    all_sections = [
        ("vc-helpers", vc_helpers),
        ("vc-spec", vc_spec), 
        ("vc-code", vc_code),
    ]
    
    # Only validate theorem and proof sections if not in spec mode
    # (in spec mode, these are templates and may contain sorry)
    if not spec_mode:
        all_sections.extend([
            ("vc-theorem", vc_theorem),
            ("vc-proof", vc_proof)
        ])
    
    for section_name, content in all_sections:
        if not content:
            continue
            
        # Check for verification bypasses and cheating patterns
        cheat_patterns = [
            # Direct verification bypasses
            (r'\bsorry\b', "uses 'sorry' to bypass verification"),
            (r'\badmit\b', "uses 'admit' to bypass verification"), 
            (r'\bomit\b', "uses 'omit' to bypass verification"),
            
            # Axiom abuse (should be very rare in exercises)
            (r'\baxiom\b', "introduces new axioms which bypass verification"),
            (r'\bpostulate\b', "uses 'postulate' which bypasses verification"),
            
            # Unsafe tactics and operations
            (r'\bunsafe\b', "uses 'unsafe' operations"),
            (r'\bcast\b', "uses potentially unsafe 'cast' operations"),
            (r'\bClassical\.choose\b', "uses Classical.choose without proper justification"),
            
            # Meta-programming that could bypass verification
            (r'\bmeta\b', "uses meta-programming which could bypass verification"),
            (r'\b#check\b.*sorry', "uses #check with sorry"),
            (r'\b#eval\b.*sorry', "uses #eval with sorry"),
            
            # Tactic cheats
            (r'\bskip\b', "uses 'skip' tactic to bypass proof obligations"),
            (r'\bexact_mod_cast\b.*sorry', "uses exact_mod_cast with sorry"),
            
            # Dangerous imports or modules
            (r'import.*Unsafe', "imports unsafe modules"),
            (r'import.*Meta\.Unsafe', "imports meta unsafe modules"),
            
            # Classical logic abuse patterns  
            (r'\bClassical\.em\b.*sorry', "uses Classical.em with sorry"),
            (r'\bby_contra\b.*sorry', "uses by_contra with sorry"),
            
            # Proof by assertion patterns
            (r'\bhave.*:=.*sorry', "uses 'have' with sorry"),
            (r'\bsuffices.*sorry', "uses 'suffices' with sorry"),
            
            # Loop/recursion cheats
            (r'\bpartial\b.*def', "uses 'partial def' which bypasses termination checking"),
            (r'\bnoncomputable\b.*sorry', "uses 'noncomputable' with sorry"),
            
            # Type system bypasses
            (r'\bUnchecked\.cast', "uses Unchecked.cast which bypasses type checking"),
            
            # Native code execution that could bypass verification
            (r'@\[extern\]', "uses extern functions that bypass verification"),
            (r'@\[implementedBy\]', "uses implementedBy which could bypass verification"),
        ]
        
        for pattern, reason in cheat_patterns:
            if re.search(pattern, content, re.IGNORECASE | re.MULTILINE):
                return f"Section {section_name} {reason}"
    
    # Additional checks for proof quality
    if vc_proof:
        # Check for proof scripts that are just tactic spam without structure
        tactic_spam_patterns = [
            r'(simp\s*;?\s*){8,}',  # Too many simp calls
            r'(rw\s*\[.*?\]\s*;?\s*){15,}',  # Too many rewrites
            r'(apply\s+\w+\s*;?\.yaml for s*){10,}',  # Too many applies
        ]
        
        for pattern in tactic_spam_patterns:
            if re.search(pattern, vc_proof, re.MULTILINE):
                return f"Proof section contains suspicious tactic repetition that might indicate automated proof search rather than understanding"
    
    return None


def _format_errors(validation_error: Optional[str], generation_error: Optional[str], verification, for_prompt: bool = False) -> Optional[str]:
    """Format errors for LLM prompt or logging.
 
    Args:
        validation_error: Validation error message if any
        generation_error: Generation error message if any  
        verification: Verification result object
        for_prompt: If True, format for LLM prompt; if False, for logging
    
    Returns:
        Formatted error string, or None if no errors (when not for_prompt)
    """
    error_parts = []
    prefix = "error:" if for_prompt else ":"
    
    if validation_error:
        error_parts.append(f"Validation{prefix} {validation_error}")
    if generation_error:
        error_parts.append(f"Generation{prefix} {generation_error}")
    if verification and verification.error:
        error_parts.append(f"Verification{prefix} {verification.error}")
    elif verification is None and (for_prompt or (not validation_error and not generation_error)):
        error_parts.append("No code generated or verification failed" if for_prompt else "No code generated")
    
    if error_parts:
        return "; ".join(error_parts)
    elif for_prompt:
        return "Unknown error"
    else:
        return None


def get_mode_flags(mode: str) -> tuple[bool, bool]:
    """Convert mode string to (spec, vibe) boolean flags.
    
    Args:
        mode: One of 'spec', 'vibe', or 'specvibe'
        
    Returns:
        Tuple of (spec_flag, vibe_flag)
    """
    if mode == "spec":
        return True, False
    elif mode == "vibe":
        return False, True
    elif mode == "specvibe":
        return True, True
    else:
        raise ValueError(f"Invalid mode: {mode}. Must be one of 'spec', 'vibe', 'specvibe'")


@dataclass
class IterationData:
    """Data for a single iteration."""
    file_path: str
    iteration: int
    success: bool
    vc_spec: str
    vc_code: str
    verifier_message: str
    timestamp: float

@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool  # True if the generated code is verified
    spec_yaml_file: str  # YAML specification file path 
    code_yaml_file: str  # YAML generated code file path 
    code_file: str  # generated code file path
    error: str | None     # Error message if the generated code is not verified
    iterations: list[IterationData]  # All iterations performed for this file


def process_spec(
    config: ProcessingConfig, prompt_loader: PromptLoader, llm_provider, file_path: str
) -> ProcessingResult:
    # Create artifact for storing generated files
    file_key = Path(file_path).stem
    artifact = wandb_utils.create_file_artifact(f"files_{file_key}", "verification_files")
    iterations_data = []  # Collect iteration data to return
     
    try: 
        logger.info(f"Processing: {file_path}")
        output_path, code_output_path, _ = prepare_output_paths(config, Path(file_path))

        yaml = load_yaml(Path(file_path))
        spec_mode, vibe_mode = get_mode_flags(config.mode)
        original_spec = yaml.get("vc-spec", "")
        # Build initial code
        code = yaml_to_code(yaml, spec_mode=spec_mode, vibe_mode=vibe_mode, language=config.language)
        
        verification = None
        validation_error = None
        generation_error = None

        iteration = 1
        while iteration <= config.max_iterations:
            logger.info(f" Vericoding iteration {iteration}:")
            
            # Create prompt based on previous iteration's errors
            if iteration == 1:
                prompt = prompt_loader.format_prompt("generate_code", code=code)
            else:
                error_details = _format_errors(validation_error, generation_error, verification, for_prompt=True)
                prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=code,
                    errorDetails=error_details,
                    iteration=iteration,
                )
            
            # Reset error tracking for current iteration
            validation_error = None
            generation_error = None
            verification = None
            
            try:
                llm_response = call_llm(llm_provider, config, prompt, wandb=wandb_utils.enabled())              
                if not llm_response or not str(llm_response).strip():
                    # Empty response: save raw and retry WITHOUT counting this iteration
                    logger.info("    ✗ Empty LLM response; not counting this iteration, retrying...")
                    try:
                        save_iteration_code(
                            config,
                            None,
                            iteration,
                            llm_response or "",
                            "raw",
                            None,
                            Path(file_path)
                        )
                    except Exception:
                        pass
                    try:
                        time.sleep(1.0)
                    except Exception:
                        pass
                    continue
                # Parse LLM response using generic section extraction
                vc_helpers, vc_spec, vc_code, vc_theorem, vc_proof = extract_sections(llm_response)

                # Validate the extracted sections
                validation_error = validate_sections(vc_helpers, vc_spec, vc_code, vc_theorem, vc_proof, config.language, spec_mode)
                if validation_error:
                    logger.info(f"    ✗ Validation error: {validation_error}")
                    # Save reconstructed Lean file to help debugging validation errors
                    try:
                        # Update sections with the extracted content (even if invalid)
                        update_sections(yaml, vc_helpers, vc_code, vc_spec, vc_theorem, vc_proof, spec_mode=spec_mode, language=config.language)
                        # Generate the full reconstructed code
                        reconstructed_code = yaml_to_code(yaml, spec_mode=True, vibe_mode=vibe_mode, language=config.language)
                        save_iteration_code(
                            config,
                            None,
                            iteration,
                            reconstructed_code,
                            "validation_failed",
                            None,
                            Path(file_path)
                        )
                        logger.info(f"    💾 Saved reconstructed code to: debug/{Path(file_path).stem}_iter_{iteration}_validation_failed.lean")
                    except Exception:
                        # Fallback to raw response if reconstruction fails
                        try:
                            save_iteration_code(
                                config,
                                None,
                                iteration,
                                llm_response or "",
                                "raw",
                                None,
                                Path(file_path)
                            )
                            logger.info(f"    💾 Saved raw response to: debug/{Path(file_path).stem}_iter_{iteration}_raw.lean")
                        except Exception:
                            pass
                else:
                    # don't allow spec to change if in spec mode
                    if spec_mode:
                        vc_spec = original_spec
                    update_sections(yaml, vc_helpers, vc_code, vc_spec, vc_theorem, vc_proof, spec_mode=spec_mode, language=config.language)
                    # we always include spec after the first iteration
                    code = yaml_to_code(yaml, spec_mode=True, vibe_mode=vibe_mode, language=config.language)
                    logger.info(f"    Done generating code at iteration {iteration}")
                        
                    save_iteration_code(config, None, iteration, code, "current", str(code_output_path), Path(file_path))
                    verification = verify_file(config, str(code_output_path))
            except Exception as e:
                logger.info(f"    ✗ Failed to generate code: {str(e)}")
                generation_error = str(e)
                # For empty-response style errors, retry without counting
                if "Empty response" in generation_error or "empty response" in generation_error.lower():
                    try:
                        time.sleep(1.0)
                    except Exception:
                        pass
                    continue
            
            # Always log iteration data (both successful and failed attempts)
            iteration_success = verification.success if verification else False
            error_msg = _format_errors(validation_error, generation_error, verification, for_prompt=False)
            
            wandb_utils.log_iteration(
                file_path=file_path,
                iteration=iteration,
                success=iteration_success,
                yaml_dict=yaml,
                code_output_path=str(code_output_path),
                error_msg=error_msg,
                is_final=(iteration == config.max_iterations),
                artifact=artifact,
                iterations_data=iterations_data
            )
            
            # Check if we succeeded and can break out of the loop
            if verification and verification.success:
                logger.info("    ✓ Verification successful!")
                break
            else:
                # Log the failure reason and continue to next iteration
                if verification and verification.error:
                    logger.info(f"    ✗ Verification failed: {verification.error[:200]}...")
                elif validation_error:
                    logger.info(f"    ✗ Validation failed: {validation_error}, will retry in next iteration")
                elif generation_error:
                    logger.info(f"    ✗ Code generation failed: {generation_error}, will retry in next iteration")
                else:
                    logger.info("    ✗ Unknown error occurred, will retry in next iteration")

            iteration += 1

        
        if verification and verification.success:
            logger.info(f"  ✓ Successfully generated and verified: {output_path.name}")
            success = True
            error_msg = None
        else:
            error_msg = verification.error if verification else "Unknown verification error"
            logger.info(
                f"  ✗ Failed to verify after {config.max_iterations} iterations: {error_msg[:200] if error_msg else 'Unknown error'}..."
            )
            success = False
            
        return ProcessingResult(
            success=success,
            spec_yaml_file=str(file_path),
            code_yaml_file=str(output_path),
            code_file=str(code_output_path),
            error=error_msg,
            iterations=iterations_data,
        )

    except Exception as e:
        logger.info(f"✗ Failed: {Path(file_path).name} - {str(e)}")
        wandb_utils.log_exception(file_path)
        success = False
        error_msg = str(e)
        
        return ProcessingResult(
            success=success,
            spec_yaml_file=str(file_path),
            code_yaml_file=str(output_path),
            code_file=str(code_output_path),
            error=error_msg,
            iterations=iterations_data,
        )
    finally:
        # Log artifact with generated files
        wandb_utils.log_artifact(artifact)


def process_files_parallel(
    config: ProcessingConfig, prompt_loader: PromptLoader, llm_provider, spec_files: list[str]
) -> list[ProcessingResult]:
    """Process files in parallel using ThreadPoolExecutor."""
    results = []
    completed_count = 0
    total_files = len(spec_files)

    print(
        f"Processing {total_files} files using {config.max_workers} parallel workers..."
    )
    print("")

    # Create iteration table for all data
    iteration_table = wandb_utils.create_iteration_table()

    with ThreadPoolExecutor(max_workers=config.max_workers) as executor:
        # Submit all tasks
        future_to_file = {
            executor.submit(
                process_spec, config, prompt_loader, llm_provider, file_path
            ): file_path
            for file_path in spec_files
        }

        # Process completed tasks as they finish
        for future in as_completed(future_to_file):
            file_path = future_to_file[future]
            completed_count += 1

            result = future.result()
            results.append(result)

            # Print progress update
            status = "✓" if result.success else "✗"
            logger.info(
                f"[{completed_count}/{total_files}] {status} {Path(file_path).name}"
            )
            
            # Add iteration data to table as each task completes
            for iteration_data in result.iterations:
                wandb_utils.add_iteration_row(
                    iteration_table,
                    iteration_data.file_path,
                    iteration_data.iteration,
                    iteration_data.success,
                    iteration_data.vc_spec,
                    iteration_data.vc_code,
                    iteration_data.verifier_message,
                )

    # Log the completed iteration table
    wandb_utils.log_table_if_any(iteration_table, "verification_iterations")

    return results
