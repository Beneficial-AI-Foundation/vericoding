import argparse
import asyncio
import os
import re
import subprocess
import tempfile
import sys
from pathlib import Path
import random
from dotenv import load_dotenv
import yaml
from datasets import load_dataset
from pydantic_ai import Agent, ModelHTTPError
import logfire

from code2verus.config import system_prompt, cfg, ARTIFACTS
from code2verus.tools import verus_tool, dafny_tool

load_dotenv()

# Configure Logfire only if authentication is available
try:
    logfire.configure()
    logfire.instrument_pydantic_ai()
    print("Logfire configured successfully")
except Exception as e:
    print(f"Logfire configuration skipped: {e}")
    # Continue without Logfire logging


def check_verus_availability():
    """Check if Verus is available and working"""
    verus_path = cfg.get("verus_path", "verus")
    
    try:
        # Try to run verus with --version flag
        result = subprocess.run(
            [verus_path, "--version"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        
        if result.returncode == 0:
            version_info = result.stdout.strip()
            print(f"Verus found: {version_info}")
            return True
        else:
            print(f"Error: Verus command failed with return code {result.returncode}")
            if result.stderr:
                print(f"Stderr: {result.stderr}")
            return False
            
    except FileNotFoundError:
        print(f"Error: Verus executable not found at '{verus_path}'")
        print("Please ensure Verus is installed and available in your PATH, or update the verus_path in config.yml")
        return False
    except subprocess.TimeoutExpired:
        print("Error: Verus command timed out")
        return False
    except Exception as e:
        print(f"Error checking Verus availability: {e}")
        return False


def extract_rust_code(text: str) -> str:
    """Extract Rust code from markdown code blocks in the agent output"""
    # Pattern to match ```rust ... ``` blocks
    rust_pattern = r"```rust\s*\n(.*?)\n```"
    matches = re.findall(rust_pattern, text, re.DOTALL)

    if matches:
        # Return the first Rust code block found
        return matches[0].strip()

    # If no ```rust blocks found, try ```verus
    verus_pattern = r"```verus\s*\n(.*?)\n```"
    matches = re.findall(verus_pattern, text, re.DOTALL)

    if matches:
        # Return the first Verus code block found
        return matches[0].strip()

    # If no specific blocks found, try generic ```
    generic_pattern = r"```\s*\n(.*?)\n```"
    matches = re.findall(generic_pattern, text, re.DOTALL)

    if matches:
        # Look for the longest code block that looks like Rust/Verus code
        for match in matches:
            code = match.strip()
            # Check if it looks like Rust/Verus code (contains common keywords)
            if any(keyword in code for keyword in ['fn ', 'use ', 'impl ', 'struct ', 'requires', 'ensures', 'proof']):
                return code
        # If no good match, return the first one
        return matches[0].strip()

    # If no code blocks found, return the original text
    return text.strip()


def create_agent(source_language: str = "dafny"):
    """Create and return a configured PydanticAI agent with tools"""
    # Load language-specific system prompt
    language_prompt = cfg.get("system_prompts", {}).get(source_language.lower(), system_prompt)
    
    return Agent(
        cfg["model"],
        name="code2verus",
        deps_type=str,
        output_type=str,
        tools=[verus_tool, dafny_tool],
        system_prompt=language_prompt,
        retries=10,
    )


async def translate_code_to_verus(source_code: str, source_language: str = "dafny") -> tuple[str, int]:
    """Translate source code to Verus using the agent"""
    agent = create_agent(source_language)

    user_prompt = f"""
Please translate the following {source_language} code to Verus:

```{source_language.lower()}
{source_code}
```

Use the `verus` tool to make sure your output compiles. 

IMPORTANT: In your response, include the final Verus code in a code block marked with ```rust or ```verus. Do not include explanations or summaries in the code block - only the executable Verus code.
"""

    result = await agent.run(user_prompt, deps=source_code)

    # Extract only the Rust code from the agent's output
    rust_code = extract_rust_code(result.output)
    num_iterations = len(result.all_messages()) // 3

    return rust_code, num_iterations


def load_benchmark(benchmark: str = "wendy-sun/DafnyBench", split: str = "test"):
    """Load the specified benchmark dataset from Hugging Face"""
    logfire.info(f"Loading {benchmark} dataset (split: {split})...")
    dataset = load_dataset(benchmark, split=split)
    return dataset


def is_sample_already_successful(relative_path: Path, benchmark_name: str = "dafnybench") -> bool:
    """Check if a sample already has success: true in its success.yml file"""
    artifact_path = ARTIFACTS / benchmark_name / relative_path.parent
    success_file = artifact_path / "success.yml"

    if not success_file.exists():
        return False

    try:
        with open(success_file, "r") as success_yaml:
            data = yaml.safe_load(success_yaml)
        return data.get("success", False)
    except Exception:
        return False


async def verify_verus_code(verus_code: str) -> tuple[bool, str, str]:
    """Async function to verify Verus code"""
    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".rs", delete=False
    ) as tmpfile:
        tmpfile.write(verus_code)
        temp_file = tmpfile.name

    try:
        # Run verus verification in a separate process
        process = await asyncio.create_subprocess_exec(
            cfg["verus_path"], temp_file,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        
        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=30.0)
            verification_success = process.returncode == 0
            verification_output = stdout.decode('utf-8') if stdout else ""
            verification_error = stderr.decode('utf-8') if stderr else ""
        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            verification_success = False
            verification_output = ""
            verification_error = "Verus verification timed out after 30 seconds"
            
    except OSError as exc:
        verification_success = False
        verification_output = ""
        verification_error = f"Error running Verus: {str(exc)}"
    finally:
        # Clean up temporary file
        try:
            os.unlink(temp_file)
        except OSError:
            pass

    return verification_success, verification_output, verification_error


async def process_item(
    idx: int, item: dict, source_language: str = "dafny", benchmark_name: str = "dafnybench", max_retries: int = 32, base_delay: float = 5.0
) -> dict:
    """Process a single item from the dataset with exponential backoff"""
    
    # Handle different dataset structures
    if "ground_truth" in item:
        # DafnyBench format
        source_code = item["ground_truth"]
        source_filename = Path(item["test_file"])
        # Preserve the directory structure but change extension to .rs
        relative_path = source_filename.with_suffix('.rs')
    elif "org_input" in item:
        # ReForm-DafnyComp-Benchmark format
        source_code = item["org_input"]
        # Generate filename from item ID, preserve any directory structure
        source_filename = Path(f"item_{item.get('org_input_id', idx)}.dfy")
        relative_path = source_filename.with_suffix('.rs')
    elif "id" in item and "lean_code" in item:
        # Verina format (sunblaze-ucb/verina)
        source_code = item["lean_code"]
        # Use the actual ID from the dataset (e.g., "verina_basic_70")
        source_filename = Path(f"{item['id']}.lean")
        # Create a directory for each item
        relative_path = Path(item['id']) / source_filename.with_suffix('.rs').name
    else:
        # Fallback for unknown formats
        source_code = item.get("code", item.get("source", ""))
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix('.rs')
    
    artifact_path = ARTIFACTS / benchmark_name / relative_path.parent
    output_filename = relative_path.name

    # Check if this sample already succeeded
    if is_sample_already_successful(relative_path.with_suffix(''), benchmark_name):
        logfire.info(f"Skipping item {idx + 1}: {source_filename} (already successful)")
        return {"path": artifact_path, "success": True}

    logfire.info(f"Processing item {idx + 1}: {source_filename} ({source_language})")
    artifact_path.mkdir(parents=True, exist_ok=True)

    # Exponential backoff retry logic
    for attempt in range(max_retries + 1):
        try:
            verus_code, num_iterations = await translate_code_to_verus(source_code, source_language)
            verus_output_path = artifact_path / output_filename
            with open(verus_output_path, "w") as verus_file:
                verus_file.write(verus_code)
            logfire.info(f"Generated Verus code saved to: {verus_output_path}")

            # Use async verification
            verification_success, verification_output, verification_error = await verify_verus_code(verus_code)

            info = {
                "success": verification_success,
                "num_iterations": num_iterations,
                "verification_output": verification_output,
                "verification_error": verification_error,
            }
            with open(artifact_path / "success.yml", "w") as success_file:
                yaml.dump(
                    info,
                    success_file,
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


async def check_existing_success(idx: int, item: dict, benchmark_name: str) -> bool:
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
    else:
        # Fallback for unknown formats
        source_filename = Path(f"item_{idx}.dfy")
        relative_path = source_filename.with_suffix('')
        
    return is_sample_already_successful(relative_path, benchmark_name)


async def main_async(benchmark: str = "wendy-sun/DafnyBench", split: str = "test", source_language: str = "dafny", max_concurrent: int = 3) -> None:
    """Async main function for parallel processing"""
    print("Code2Verus translator initialized!")

    # Load the dataset
    dataset = load_benchmark(benchmark, split)
    
    # Extract benchmark name for artifact path
    benchmark_name = benchmark.split("/")[-1].lower().replace("-", "")

    # Check for existing successful samples in parallel
    print("Checking for existing successful samples...")
    existing_success_checks = [
        check_existing_success(idx, item, benchmark_name) 
        for idx, item in enumerate(dataset)
    ]
    existing_success_results = await asyncio.gather(*existing_success_checks)
    skipped_count = sum(existing_success_results)

    # Limit concurrent API calls to prevent rate limiting
    semaphore = asyncio.Semaphore(max_concurrent)

    async def process_with_semaphore(idx: int, item: dict) -> dict:
        async with semaphore:
            return await process_item(idx, item, source_language, benchmark_name)

    item_processes = [
        process_with_semaphore(idx, item) for idx, item in enumerate(dataset)
    ]
    # Process all items in parallel using asyncio.gather and list comprehension
    results = await asyncio.gather(*item_processes)

    with open(ARTIFACTS / f"{benchmark_name}_results.yml", "w") as results_file:
        yaml.dump(results, results_file)

    # Calculate statistics
    total_successful = sum(res["success"] for res in results)
    newly_successful = sum(
        res["success"] for res in results if not res.get("skipped", False)
    )
    percentage_successful = total_successful / len(results)

    print("Results:")
    print(f"  Previously successful: {skipped_count}")
    print(f"  Newly successful: {newly_successful}")
    print(f"  Total successful: {total_successful}")
    print(f"  Overall success rate: {100 * percentage_successful:.1f}%")


def main() -> None:
    """Main entry point for code2verus"""
    parser = argparse.ArgumentParser(
        description="Translate code from various verification languages to Verus using AI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  code2verus                                            # Use default DafnyBench (test split, dafny)
  code2verus --benchmark wendy-sun/DafnyBench --language dafny  # Specify language explicitly  
  code2verus --benchmark sunblaze-ucb/verina --language lean --split train  # Use Verina benchmark with Lean
  code2verus --benchmark other-user/CustomBench --language dafny --split test # Use different benchmark
  code2verus --max-concurrent 5                        # Allow 5 concurrent translations
        """
    )
    parser.add_argument(
        "--benchmark",
        default="wendy-sun/DafnyBench",
        help="Hugging Face dataset path for the benchmark (default: wendy-sun/DafnyBench)"
    )
    parser.add_argument(
        "--split",
        default="test",
        help="Dataset split to use (default: test)"
    )
    parser.add_argument(
        "--language",
        default="dafny",
        choices=["dafny", "lean"],
        help="Source language to translate from (default: dafny)"
    )
    parser.add_argument(
        "--max-concurrent",
        type=int,
        default=3,
        help="Maximum number of concurrent translations (default: 3)"
    )
    
    args = parser.parse_args()
    
    # Check if Verus is available before proceeding
    if not check_verus_availability():
        print("\nFailed to find or run Verus. Please ensure:")
        print("1. Verus is installed and working")
        print("2. The verus_path in config.yml is correct")
        print("3. Verus is in your PATH if using the default 'verus' command")
        sys.exit(1)
    
    print(f"Using benchmark: {args.benchmark} (split: {args.split})")
    print(f"Source language: {args.language}")
    print(f"Max concurrent translations: {args.max_concurrent}")
    
    asyncio.run(main_async(args.benchmark, args.split, args.language, args.max_concurrent))
