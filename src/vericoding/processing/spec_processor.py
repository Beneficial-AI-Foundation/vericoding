
import logging
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path

from vericoding.core.config import ProcessingConfig
from vericoding.core.llm_providers import call_llm
from vericoding.core.prompts import PromptLoader
from vericoding.core.language_tools import verify_file
from vericoding.utils.io_utils import prepare_output_paths, save_iteration_code
from vericoding.processing.yaml_processor import load_yaml, yaml_to_code, extract_sections, update_sections, save_yaml
from vericoding.utils import wandb_utils

logger = logging.getLogger(__name__)


@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool  # True if the generated code is verified
    spec_yaml_file: str  # YAML specification file path 
    code_yaml_file: str  # YAML generated code file path 
    code_file: str  # generated code file path
    error: str | None     # Error message if the generated code is not verified


def process_spec(
    config: ProcessingConfig, prompt_loader: PromptLoader, llm_provider, file_path: str
) -> ProcessingResult:
    
    iteration_table = wandb_utils.create_iteration_table()
    
    # Create artifact for storing generated files
    file_key = Path(file_path).stem
    artifact = wandb_utils.create_file_artifact(f"files_{file_key}", "verification_files")
     
    try: 
        logger.info(f"Processing: {file_path}")
        output_path, code_output_path, _ = prepare_output_paths(config, Path(file_path))

        yaml = load_yaml(Path(file_path))
        code = yaml_to_code(yaml)  # Current generated code
        
        verification = None

        for iteration in range(1, config.max_iterations + 1):
            logger.info(f" Vericoding iteration {iteration}:") 
            if iteration == 1:
                prompt = prompt_loader.format_prompt("generate_code", code=code)
            else:
                error_details = verification.error or "Unknown error"
                prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=code,
                    errorDetails=error_details,
                    iteration=iteration,
                )
            try:
                llm_response = call_llm(llm_provider, config, prompt, wandb=wandb_utils.enabled())              
                vc_helpers, vc_code = extract_sections(llm_response)
                
                if vc_helpers or vc_code:
                    update_sections(yaml, vc_helpers, vc_code)
                    code = yaml_to_code(yaml)
                    logger.info(f"    Done generating code at iteration {iteration}")
                    
                    save_iteration_code(config, None, iteration, code, "current", str(code_output_path), Path(file_path))
                    verification = verify_file(config, str(code_output_path))
                else:
                    logger.warning("    No valid code sections found in LLM response")
                    verification = None
                    
            except Exception as e:
                logger.info(f"    ✗ Failed to generate code: {str(e)}")
                break
            
            wandb_utils.log_iteration(
                file_path=file_path,
                iteration=iteration,
                success=verification.success if verification else False,
                yaml_dict=yaml,
                code_output_path=str(code_output_path),
                error_msg=verification.error if verification else "No code generated",
                is_final=(iteration == config.max_iterations),
                iteration_table=iteration_table,
                artifact=artifact
            )

            if verification and verification.success:
                logger.info("    ✓ Verification successful!")
                break
            elif verification:
                logger.info(
                    f"    ✗ Verification failed: {verification.error[:200] if verification.error else 'Unknown error'}..."
                )
            else:
                logger.info("    ✗ No code generated, skipping verification")
                break

        save_yaml(output_path, yaml)
        wandb_utils.add_files_to_artifact(artifact, [ (str(output_path), f"{file_key}_final.yaml")])
        
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
        )
    finally:
        # Log the iteration table if we have any data
        wandb_utils.log_table_if_any(iteration_table)
        
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

    return results
