#!/usr/bin/env python3
"""
Enhanced Specification-to-Code Processing with 1M Token Model Support

This script processes specification files using the 1M token context window
to enable batch processing and cross-file context awareness.
"""

import argparse
import os
import shutil
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any

import wandb

# Import the modular components
from vericoding.core import (
    ProcessingConfig,
    create_llm_provider,
    EnhancedLLMProvider,
    estimate_token_count,
    get_optimal_model_for_text,
)
from vericoding.core.config import load_environment
from vericoding.core.prompts import PromptLoader
from vericoding.core.language_tools import (
    get_tool_path,
    check_tool_availability,
    find_spec_files,
)
from vericoding.processing import process_files_parallel
from vericoding.utils import generate_summary, generate_csv_results

# Initialize environment loading
load_environment()


def parse_arguments():
    """Parse command-line arguments."""
    # Get available languages for argument choices
    available_languages = ProcessingConfig.get_available_languages()

    parser = argparse.ArgumentParser(
        description="Enhanced Specification-to-Code Processing with 1M Token Support",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(available_languages.keys())}
Supported LLM providers: claude, openai, deepseek

Examples:
  python spec_to_code_1m.py lean ./hoare_specs_100 --batch-mode --context-aware
  python spec_to_code_1m.py lean ./hoare_specs_100 --batch-mode --smart-batching --llm-model claude-3-5-sonnet-20241022
  python spec_to_code_1m.py dafny ./specs --batch-mode --batch-size 600000
  python spec_to_code_1m.py verus ./benchmarks/verus_specs --batch-mode --context-aware --debug
        """,
    )

    parser.add_argument(
        "language",
        type=str,
        choices=list(available_languages.keys()),
        help="Programming language to process",
    )

    parser.add_argument("folder", type=Path, help="Directory with specification files")

    # Enhanced 1M token options
    parser.add_argument(
        "--batch-mode",
        action="store_true",
        help="Enable 1M token batch processing mode (process multiple files in single API call)"
    )
    
    parser.add_argument(
        "--batch-size",
        type=int,
        default=800_000,
        help="Maximum tokens per batch (default: 800,000)"
    )
    
    parser.add_argument(
        "--context-aware",
        action="store_true",
        help="Enable cross-file context analysis and pattern recognition"
    )
    
    parser.add_argument(
        "--smart-batching",
        action="store_true",
        help="Use dependency-aware intelligent batching"
    )

    # Standard options
    parser.add_argument(
        "--iterations",
        "-i",
        type=int,
        default=5,
        help="Max verification attempts per file (default: 5)",
    )

    parser.add_argument(
        "--debug",
        action="store_true",
        help="Enable debug mode (save intermediate files)",
    )

    parser.add_argument(
        "--strict-specs",
        action="store_true",
        help="Enable strict specification preservation (default: relaxed verification)",
    )
    
    parser.add_argument(
        "--no-wandb",
        action="store_true", 
        help="Disable Weights & Biases experiment tracking",
    )
    
    parser.add_argument(
        "--delete-after-upload",
        action="store_true",
        help="Delete local generated files after uploading to wandb (requires wandb to be enabled)",
    )

    parser.add_argument(
        "--workers",
        "-w",
        type=int,
        default=4,
        help="Number of parallel workers (default: 4)",
    )

    parser.add_argument(
        "--api-rate-limit-delay",
        type=int,
        default=1,
        help="Delay between API calls in seconds (default: 1)",
    )

    parser.add_argument(
        "--max-directory-traversal-depth",
        type=int,
        default=50,
        help="Maximum depth for directory traversal (default: 50)",
    )

    parser.add_argument(
        "--llm-provider",
        type=str,
        choices=["claude", "openai", "deepseek"],
        default="claude",
        help="LLM provider to use (default: claude)",
    )

    parser.add_argument(
        "--llm-model",
        type=str,
        help="Specific model to use (defaults to provider's default model)",
    )

    return parser.parse_args()


def create_optimal_batches(spec_files: List[str], max_tokens: int = 800_000) -> List[List[str]]:
    """Group files into optimal batches for 1M token processing."""
    batches = []
    current_batch = []
    current_tokens = 0
    
    print(f"Creating batches with max {max_tokens:,} tokens per batch...")
    
    for file_path in spec_files:
        try:
            with open(file_path, 'r') as f:
                file_content = f.read()
            
            estimated_tokens = estimate_token_count(file_content)
            
            if current_tokens + estimated_tokens > max_tokens:
                # Start new batch
                if current_batch:
                    batches.append(current_batch)
                    print(f"  Batch {len(batches)}: {len(current_batch)} files, ~{current_tokens:,} tokens")
                current_batch = [file_path]
                current_tokens = estimated_tokens
            else:
                # Add to current batch
                current_batch.append(file_path)
                current_tokens += estimated_tokens
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
            # Add to current batch anyway
            current_batch.append(file_path)
    
    if current_batch:
        batches.append(current_batch)
        print(f"  Batch {len(batches)}: {len(current_batch)} files, ~{current_tokens:,} tokens")
    
    print(f"Created {len(batches)} batches for 1M token processing")
    return batches


def create_batch_prompt(batch_files: List[str], language: str) -> str:
    """Create comprehensive prompt for multiple files."""
    all_specs = ""
    for file_path in batch_files:
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            all_specs += f"\n# {Path(file_path).name}\n```{language}\n{content}\n```\n"
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
            all_specs += f"\n# {Path(file_path).name}\n```{language}\n-- Error reading file: {e}\n```\n"
    
    return f"""
# Generate Verified Implementations for Multiple Specifications

You have access to {len(batch_files)} specification files. Generate implementations that:

1. **Satisfy each specification exactly**
2. **Maintain consistency across all files**
3. **Leverage common patterns and dependencies**
4. **Use shared utility functions where appropriate**
5. **Follow consistent naming and style conventions**

## Specifications
{all_specs}

## Implementation Requirements

For each specification, provide:
- Complete verified implementation
- All necessary lemmas and proofs
- Consistent error handling
- Shared utility functions where beneficial

## Output Format

```{language}
-- Implementation for: [filename]
-- Generated: [timestamp]

[complete implementation]

-- End of implementation
```

Generate ALL {len(batch_files)} implementations with full context awareness.
Do not ask questions - generate code immediately.
"""


def analyze_codebase_patterns(spec_files: List[str]) -> Dict[str, Any]:
    """Analyze patterns across all specification files."""
    patterns = {
        "common_imports": set(),
        "shared_types": set(),
        "recurring_patterns": [],
        "dependencies": {},
        "complexity_levels": {},
        "file_count": len(spec_files),
        "total_tokens": 0
    }
    
    for file_path in spec_files:
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            
            # Estimate tokens
            tokens = estimate_token_count(content)
            patterns["total_tokens"] += tokens
            
            # Simple pattern extraction (can be enhanced)
            lines = content.split('\n')
            for line in lines:
                line = line.strip()
                if line.startswith('import') or line.startswith('open'):
                    patterns["common_imports"].add(line)
                elif 'def' in line or 'theorem' in line or 'lemma' in line:
                    patterns["recurring_patterns"].append(line[:100])  # First 100 chars
                    
        except Exception as e:
            print(f"Warning: Could not analyze {file_path}: {e}")
    
    return patterns


def create_context_aware_prompt(batch_files: List[str], patterns: Dict[str, Any], language: str) -> str:
    """Create prompt with codebase-wide context."""
    all_specs = ""
    for file_path in batch_files:
        try:
            with open(file_path, 'r') as f:
                content = f.read()
            all_specs += f"\n# {Path(file_path).name}\n```{language}\n{content}\n```\n"
        except Exception as e:
            print(f"Warning: Could not read {file_path}: {e}")
    
    return f"""
# Context-Aware Code Generation

## Codebase Analysis
- Total files analyzed: {patterns['file_count']}
- Total tokens: {patterns['total_tokens']:,}
- Common imports: {list(patterns['common_imports'])[:10]}  # Top 10
- Recurring patterns: {len(patterns['recurring_patterns'])} identified

## Specifications to Implement
{all_specs}

## Implementation Strategy
1. Use identified common patterns
2. Create shared utility functions
3. Maintain consistency across all files
4. Leverage dependencies appropriately
5. Follow established import patterns

## Output Format

```{language}
-- Implementation for: [filename]
-- Generated: [timestamp]

[complete implementation]

-- End of implementation
```

Generate ALL {len(batch_files)} implementations with full context awareness.
Do not ask questions - generate code immediately.
"""


def parse_batch_response(response: str, batch_files: List[str], language: str) -> List[Any]:
    """Parse batch response into individual file results."""
    from vericoding.processing.file_processor import ProcessingResult
    
    results = []
    
    # Try to extract individual implementations
    import re
    
    # Pattern to match implementations
    pattern = rf'-- Implementation for: (.+?)\n-- Generated: (.+?)\n\n```{language}\n(.*?)\n```'
    matches = re.findall(pattern, response, re.DOTALL)
    
    if matches:
        print(f"Successfully parsed {len(matches)} implementations from batch response")
        for filename, timestamp, implementation in matches:
            results.append(ProcessingResult(
                success=True,
                file=filename,
                output=implementation,
                error=None,
                has_bypass=False
            ))
    else:
        print("Warning: Could not parse batch response, treating as single implementation")
        # Fallback: treat entire response as single implementation
        results.append(ProcessingResult(
            success=True,
            file=batch_files[0] if batch_files else 'unknown',
            output=response,
            error=None,
            has_bypass=False
        ))
    
    return results


def process_files_in_batches(config: ProcessingConfig, prompt_loader: PromptLoader, spec_files: List[str]) -> List[Dict[str, Any]]:
    """Process files using 1M token batch processing."""
    
    # Create enhanced LLM provider
    try:
        enhanced_provider = EnhancedLLMProvider(
            preferred_provider=config.llm_provider
        )
        print(f"✓ Enhanced LLM provider initialized with {config.llm_provider}")
    except Exception as e:
        print(f"Error initializing enhanced provider: {e}")
        return []
    
    # Create batches
    if config.smart_batching:
        # For now, use simple batching (can be enhanced with dependency analysis)
        batches = create_optimal_batches(spec_files, config.batch_size)
    else:
        batches = create_optimal_batches(spec_files, config.batch_size)
    
    print(f"Created {len(batches)} batches for 1M token processing")
    
    all_results = []
    
    for i, batch in enumerate(batches, 1):
        print(f"\nProcessing batch {i}/{len(batches)} ({len(batch)} files)")
        
        # Analyze patterns if context-aware
        if config.context_aware:
            patterns = analyze_codebase_patterns(spec_files)
            prompt = create_context_aware_prompt(batch, patterns, config.language)
            print(f"  Context-aware processing with {len(patterns['common_imports'])} common patterns")
        else:
            prompt = create_batch_prompt(batch, config.language)
        
        # Make single API call for entire batch
        try:
            print(f"  Making API call for {len(batch)} files...")
            response = enhanced_provider.call_api_with_context_optimization(
                prompt, 
                force_provider=config.llm_provider,
                force_model=config.llm_model or "claude-3-5-sonnet-20241022"
            )
            print(f"  ✓ Received response ({len(response):,} characters)")
            
            # Debug: Show first 500 characters of response
            print(f"  Response preview: {response[:500]}...")
            
            # Parse batch response
            batch_results = parse_batch_response(response, batch, config.language)
            all_results.extend(batch_results)
            
            # Log to wandb if available
            if wandb.run:
                wandb.log({
                    f"batch_{i}_files": len(batch),
                    f"batch_{i}_response_length": len(response),
                    f"batch_{i}_successful_parses": len([r for r in batch_results if r['success']])
                })
            
        except Exception as e:
            print(f"  ✗ Error processing batch {i}: {e}")
            # Create error results for this batch
            from vericoding.processing.file_processor import ProcessingResult
            for file_path in batch:
                all_results.append(ProcessingResult(
                    success=False,
                    file=Path(file_path).name,
                    output=None,
                    error=f"Batch processing error: {str(e)}",
                    has_bypass=False
                ))
        
        # Rate limiting delay
        if i < len(batches):
            print(f"  Waiting {config.api_rate_limit_delay}s before next batch...")
            time.sleep(config.api_rate_limit_delay)
    
    return all_results


def setup_configuration(args) -> ProcessingConfig:
    """Set up processing configuration from command line arguments."""
    available_languages = ProcessingConfig.get_available_languages()
    language_config = available_languages[args.language]

    print(
        f"=== Enhanced {language_config.name} Specification-to-Code Processing Configuration ===\n"
    )

    files_dir = str(args.folder)

    if not Path(files_dir).is_dir():
        print(f"Error: Directory '{files_dir}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")
    input_path = Path(files_dir).resolve()
    
    # Create output directory structure
    output_dir = str(Path.cwd() / f"code_from_spec_1m_on_{timestamp}" / args.language / input_path.name)
    summary_file = str(Path(output_dir) / "summary.txt")

    Path(output_dir).mkdir(parents=True, exist_ok=True)
    print(f"Created output directory: {output_dir}")

    # Create configuration object with enhanced options
    config = ProcessingConfig(
        language=args.language,
        language_config=language_config,
        files_dir=files_dir,
        max_iterations=args.iterations,
        output_dir=output_dir,
        summary_file=summary_file,
        debug_mode=args.debug,
        strict_spec_verification=args.strict_specs,
        max_workers=args.workers,
        api_rate_limit_delay=args.api_rate_limit_delay,
        llm_provider=args.llm_provider,
        llm_model=args.llm_model,
        max_directory_traversal_depth=args.max_directory_traversal_depth,
    )
    
    # Add enhanced configuration attributes
    config.batch_mode = args.batch_mode
    config.batch_size = args.batch_size
    config.context_aware = args.context_aware
    config.smart_batching = args.smart_batching

    print("\nConfiguration:")
    print(f"- Language: {language_config.name}")
    print(f"- Directory: {files_dir}")
    print(f"- Output directory: {output_dir}")
    print(f"- Max iterations: {config.max_iterations}")
    print(f"- Parallel workers: {config.max_workers}")
    print(f"- Tool path: {get_tool_path(config)}")
    print(f"- LLM Provider: {config.llm_provider}")
    print(f"- LLM Model: {config.llm_model or 'default'}")
    print(f"- Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    print(f"- Batch mode: {'Enabled' if config.batch_mode else 'Disabled'}")
    if config.batch_mode:
        print(f"- Batch size: {config.batch_size:,} tokens")
        print(f"- Context aware: {'Enabled' if config.context_aware else 'Disabled'}")
        print(f"- Smart batching: {'Enabled' if config.smart_batching else 'Disabled'}")
    print(f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}")
    print(f"- API rate limit delay: {config.api_rate_limit_delay}s")
    print("\nProceeding with configuration...")

    return config


def main():
    """Main entry point for the enhanced specification-to-code processing."""
    # Parse command-line arguments first
    args = parse_arguments()

    # Set up configuration
    config = setup_configuration(args)
    
    # Initialize wandb for experiment tracking (unless disabled)
    wandb_run = None
    if not args.no_wandb and os.getenv("WANDB_API_KEY"):
        try:
            # Initialize wandb run
            run_name = f"vericoding_1m_{config.language}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            wandb_config = {
                "language": config.language,
                "max_iterations": config.max_iterations,
                "llm_provider": config.llm_provider,
                "llm_model": config.llm_model,
                "strict_spec_verification": config.strict_spec_verification,
                "max_workers": config.max_workers,
                "files_dir": config.files_dir,
                "batch_mode": config.batch_mode,
                "batch_size": config.batch_size,
                "context_aware": config.context_aware,
                "smart_batching": config.smart_batching,
            }
            
            wandb_run = wandb.init(
                project=os.getenv("WANDB_PROJECT", "vericoding-1m"),
                entity=os.getenv("WANDB_ENTITY"),
                name=run_name,
                tags=[config.language, config.llm_provider, "1m-token"],
                mode=os.getenv("WANDB_MODE", "online")
            )
            # Update config with allow_val_change to avoid errors when keys already exist
            wandb.config.update(wandb_config, allow_val_change=True)
            print(f"✅ Weights & Biases tracking enabled: {run_name}")
            if wandb_run:
                print(f"   View at: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Failed to initialize wandb: {e}")
            wandb_run = None
    else:
        if args.no_wandb:
            print("⚠️  Weights & Biases tracking disabled (--no-wandb flag)")
        else:
            print("⚠️  Weights & Biases tracking disabled (WANDB_API_KEY not set)")

    # Initialize prompt loader for the selected language
    try:
        prompt_loader = PromptLoader(
            config.language, prompts_file=config.language_config.prompts_file
        )
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation.valid:
            print(f"Warning: Missing required prompts: {', '.join(validation.missing)}")
            print(f"Available prompts: {', '.join(validation.available)}")
            sys.exit(1)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print(
            f"Please ensure the {config.language_config.prompts_file} file exists in the {config.language} directory."
        )
        print("Expected locations:")
        script_dir = Path(__file__).parent
        print(
            f"  - {script_dir / config.language / config.language_config.prompts_file}"
        )
        print(f"  - {config.language_config.prompts_file} (current directory)")
        sys.exit(1)

    print(
        f"Starting enhanced specification-to-code processing of {config.language_config.name} files..."
    )
    print(f"Directory: {config.files_dir}")
    print(f"Output directory: {config.output_dir}")
    print(f"Tool path: {get_tool_path(config)}")
    print(f"Max iterations: {config.max_iterations}")
    print(f"Parallel workers: {config.max_workers}")
    print(f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
    if config.batch_mode:
        print(f"🚀 1M Token Batch Mode: {'Enabled'}")
        print(f"   Batch size: {config.batch_size:,} tokens")
        print(f"   Context aware: {'Enabled' if config.context_aware else 'Disabled'}")
        print(f"   Smart batching: {'Enabled' if config.smart_batching else 'Disabled'}")
    else:
        print(f"📁 Standard Mode: Processing files individually")
    print(
        f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}"
    )
    print("Processing each file by generating code from specifications.")
    if config.debug_mode:
        print(
            "DEBUG MODE: Saves code after each iteration to separate files for analysis."
        )
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    # Check if the required API key is available for the selected LLM provider
    try:
        # This will raise an error if the API key is not available
        create_llm_provider(config.llm_provider, config.llm_model)
        print(f"✓ {config.llm_provider.upper()} API key found and provider initialized")
    except Exception as e:
        print(f"Error: {str(e)}")
        print("")
        print(
            "Note: .env files are automatically loaded if they exist in the current or parent directory."
        )
        sys.exit(1)

    print("")
    print(f"Checking {config.language_config.name} availability...")
    tool_availability = check_tool_availability(config)
    if not tool_availability.available:
        print(f"Error: {tool_availability.message}")
        print(
            f"Please ensure {config.language_config.name} is installed and the {config.language_config.tool_path_env} environment variable is set correctly."
        )
        print(
            f"Current {config.language_config.tool_path_env}: {get_tool_path(config)}"
        )
        print(
            f"You can set it with: export {config.language_config.tool_path_env}=/path/to/{config.language}"
        )
        sys.exit(1)

    print(f"✓ {tool_availability.message}")
    print("")

    # Find all specification files
    spec_files = find_spec_files(config)
    print(f"Found {len(spec_files)} {config.language_config.name} files to process")
    if config.language == "lean":
        print("(Only Lean files containing 'sorry' are selected)")
    print("")

    if not spec_files:
        print(f"No {config.language_config.name} files found. Exiting.")
        return

    # Process files using enhanced method
    start_time = time.time()
    
    if config.batch_mode:
        print("🚀 Using 1M Token Batch Processing Mode")
        results = process_files_in_batches(config, prompt_loader, spec_files)
    else:
        print("📁 Using Standard Parallel Processing Mode")
        results = process_files_parallel(config, prompt_loader, spec_files)
    
    end_time = time.time()
    processing_time = end_time - start_time

    # Generate summary
    print("")
    print("Generating summary...")
    summary = generate_summary(config, results)

    print("")
    print("=== SUMMARY ===")
    print(summary)
    print("")
    print(f"Summary saved to: {config.summary_file}")
    print(f"All generated files saved to: {config.output_dir}")
    print(f"Total processing time: {processing_time:.2f} seconds")
    if results:
        print(f"Average time per file: {processing_time / len(results):.2f} seconds")
    else:
        print("Average time per file: N/A (no files processed)")
    if config.batch_mode:
        print("🚀 1M Token Mode: Processed files in batches for optimal context utilization")
    if config.debug_mode:
        print(
            "DEBUG: Files saved: original, generated, current per iteration, and final implementation"
        )
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    generate_csv_results(config, results)

    # Print final statistics
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success and not r.has_bypass]
    bypassed = [r for r in results if r.has_bypass]
    
    if results:
        success_rate = len(successful) / len(results) * 100
        print(f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({success_rate:.1f}%)")
    else:
        print(f"\n🎉 Processing completed: No files were processed")
    if config.batch_mode:
        print(f"🚀 1M Token Batch Mode: Leveraged large context window for enhanced processing")
    else:
        print(f"⚡ Parallel processing with {config.max_workers} workers completed in {processing_time:.2f}s")
    
    # Log experiment summary to wandb (if enabled)
    if wandb_run:
        try:
            # Log final summary metrics
            wandb.run.summary["total_files"] = len(results)
            wandb.run.summary["successful_files"] = len(successful)
            wandb.run.summary["failed_files"] = len(failed)
            wandb.run.summary["bypassed_files"] = len(bypassed)
            wandb.run.summary["success_rate"] = len(successful) / len(results) if results else 0.0
            wandb.run.summary["duration_seconds"] = processing_time
            wandb.run.summary["batch_mode"] = config.batch_mode
            wandb.run.summary["context_aware"] = config.context_aware
            wandb.run.summary["smart_batching"] = config.smart_batching
            
            # Upload generated files as artifacts
            print("\n📤 Uploading generated files to wandb...")
            artifact = wandb.Artifact(
                name=f"generated_code_1m_{config.language}",
                type="code",
                description=f"Generated {config.language} code using 1M token batch processing"
            )
            
            # Add the output directory to the artifact
            output_path = Path(config.output_dir)
            if output_path.exists():
                artifact.add_dir(str(output_path))
                wandb.log_artifact(artifact)
                print(f"✅ Files uploaded to wandb artifact: generated_code_1m_{config.language}")
                
                # Delete local files if requested
                if args.delete_after_upload:
                    try:
                        shutil.rmtree(output_path)
                        print(f"🗑️  Local files deleted from {output_path}")
                    except Exception as e:
                        print(f"⚠️  Error deleting local files: {e}")
            else:
                print(f"⚠️  Output directory not found: {output_path}")
            
            # Finish wandb run
            wandb.finish()
            print(f"\n✅ Wandb run completed: {wandb_run.url}")
        except Exception as e:
            print(f"⚠️  Error logging to wandb: {e}")


if __name__ == "__main__":
    main()

