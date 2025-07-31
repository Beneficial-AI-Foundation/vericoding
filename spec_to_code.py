#!/usr/bin/env python3
"""
Unified Specification-to-Code Processing

This script processes specification files containing declarations for Dafny, Lean, or Verus,
generates implementations using Claude API, and iteratively fixes verification errors.
"""

import argparse
import csv
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any
from urllib.parse import quote

import requests
import yaml

# Thread safety
print_lock = threading.Lock()
file_write_lock = threading.Lock()


# Configuration class to hold language-specific settings
@dataclass
class LanguageConfig:
    name: str
    file_extension: str
    tool_path_env: str
    default_tool_path: str
    prompts_file: str
    verify_command: list[str]
    compile_check_command: list[str] | None
    success_indicators: list[str]
    code_block_patterns: list[str]
    keywords: list[str]
    spec_patterns: list[str]

    @classmethod
    def from_dict(cls, config_dict: dict[str, Any]) -> "LanguageConfig":
        """Create LanguageConfig from dictionary."""
        return cls(
            name=config_dict["name"],
            file_extension=config_dict["file_extension"],
            tool_path_env=config_dict["tool_path_env"],
            default_tool_path=config_dict["default_tool_path"],
            prompts_file=config_dict["prompts_file"],
            verify_command=config_dict["verify_command"],
            compile_check_command=config_dict.get("compile_check_command"),
            success_indicators=config_dict["success_indicators"],
            code_block_patterns=config_dict["code_block_patterns"],
            keywords=config_dict["keywords"],
            spec_patterns=config_dict["spec_patterns"],
        )


@dataclass
class ToolAvailabilityResult:
    """Result of checking tool availability."""

    available: bool
    message: str


@dataclass
class VerificationResult:
    """Result of file verification."""

    success: bool
    output: str
    error: str | None


@dataclass
class ProcessingResult:
    """Result of processing a specification file."""

    success: bool
    file: str
    output: str | None
    error: str | None
    has_bypass: bool


@dataclass
class PromptValidationResult:
    """Result of prompt validation."""

    valid: bool
    missing: list[str]
    available: list[str]


@dataclass
class LanguageConfigResult:
    """Result of loading language configuration."""

    languages: dict[str, LanguageConfig]
    common_compilation_errors: list[str]


# Load language configuration
def load_language_config() -> LanguageConfigResult:
    config_path = Path(__file__).parent / "config" / "language_config.yaml"
    if not config_path.exists():
        # Fallback to looking in current directory
        config_path = Path("language_config.yaml")

    if not config_path.exists():
        raise FileNotFoundError(f"Language configuration file not found: {config_path}")

    with config_path.open() as f:
        config = yaml.safe_load(f)

    languages = {}
    for lang, settings in config.items():
        if lang != "common_compilation_errors":
            languages[lang] = LanguageConfig.from_dict(settings)

    return LanguageConfigResult(
        languages=languages, common_compilation_errors=config.get("common_compilation_errors", [])
    )


# Global variables
LANGUAGES: dict[str, LanguageConfig]
COMMON_COMPILATION_ERRORS: list[str]
_config_result = load_language_config()
LANGUAGES = _config_result.languages
COMMON_COMPILATION_ERRORS = _config_result.common_compilation_errors
CURRENT_LANGUAGE: str | None = None
LANGUAGE_CONFIG: LanguageConfig | None = None
FILES_DIR: str = ""
MAX_ITERATIONS: int = 2
OUTPUT_DIR: str = ""
SUMMARY_FILE: str = ""
DEBUG_MODE: bool = False
STRICT_SPEC_VERIFICATION: bool = False
MAX_WORKERS: int = 4
API_RATE_LIMIT_DELAY: int = 1
MAX_DIRECTORY_TRAVERSAL_DEPTH: int = 50  # Maximum depth to prevent excessive directory traversal

# Environment variables
ANTHROPIC_API_KEY: str | None = os.getenv("ANTHROPIC_API_KEY")


# Simple PromptLoader implementation
class PromptLoader:
    def __init__(self, prompts_file: str = "prompts.yaml") -> None:
        self.prompts_file: str = prompts_file
        self.prompts: dict[str, str] = {}
        self._load_prompts()

    def _load_prompts(self) -> None:
        # Get the script directory
        script_dir = Path(__file__).parent

        # First try in the language-specific directory relative to script
        if CURRENT_LANGUAGE:
            lang_prompts_path = script_dir / CURRENT_LANGUAGE / self.prompts_file
            if lang_prompts_path.exists():
                with lang_prompts_path.open() as f:
                    self.prompts = yaml.safe_load(f)
                return

        # Then try in current directory
        if Path(self.prompts_file).exists():
            with Path(self.prompts_file).open() as f:
                self.prompts = yaml.safe_load(f)
        else:
            raise FileNotFoundError(f"Prompts file not found: {self.prompts_file}")

    def format_prompt(self, prompt_name: str, **kwargs: Any) -> str:
        if prompt_name not in self.prompts:
            raise KeyError(f"Prompt '{prompt_name}' not found")
        try:
            return self.prompts[prompt_name].format(**kwargs)
        except KeyError as e:
            # Better error message for missing placeholders
            raise KeyError(f"Missing placeholder in prompt '{prompt_name}': {e}")
        except Exception as e:
            # Catch any other formatting errors
            raise ValueError(f"Error formatting prompt '{prompt_name}': {e}")

    def validate_prompts(self) -> PromptValidationResult:
        required = ["generate_code", "fix_verification"]
        missing = [p for p in required if p not in self.prompts]
        return PromptValidationResult(
            valid=len(missing) == 0, missing=missing, available=list(self.prompts.keys())
        )


def parse_arguments():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Unified Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(LANGUAGES.keys())}

Examples:
  python spec_to_code.py dafny ./specs
  python spec_to_code.py lean ./NumpySpec/DafnySpecs --iterations 3
  python spec_to_code.py verus ./benchmarks/verus_specs --debug --iterations 5
  python spec_to_code.py dafny ./specs --workers 8 --iterations 3
  python spec_to_code.py verus ./specs --workers 2 --debug --strict-specs
        """,
    )

    parser.add_argument(
        "language", type=str, choices=list(LANGUAGES.keys()), help="Programming language to process"
    )

    parser.add_argument("folder", type=str, help="Directory with specification files")

    parser.add_argument(
        "--iterations",
        "-i",
        type=int,
        default=5,
        help="Max verification attempts per file (default: 5)",
    )

    parser.add_argument(
        "--debug", action="store_true", help="Enable debug mode (save intermediate files)"
    )

    parser.add_argument(
        "--strict-specs",
        action="store_true",
        help="Enable strict specification preservation (default: relaxed verification)",
    )

    parser.add_argument(
        "--workers", "-w", type=int, default=4, help="Number of parallel workers (default: 4)"
    )

    return parser.parse_args()


def setup_configuration(args):
    global FILES_DIR, MAX_ITERATIONS, OUTPUT_DIR, SUMMARY_FILE, DEBUG_MODE
    global STRICT_SPEC_VERIFICATION, MAX_WORKERS, CURRENT_LANGUAGE, LANGUAGE_CONFIG

    CURRENT_LANGUAGE = args.language
    LANGUAGE_CONFIG = LANGUAGES[args.language]

    print(f"=== {LANGUAGE_CONFIG.name} Specification-to-Code Processing Configuration ===\n")

    FILES_DIR = args.folder

    if not Path(FILES_DIR).is_dir():
        print(f"Error: Directory '{FILES_DIR}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory outside the input directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")

    # Extract the relevant part of the input path for the output hierarchy
    input_path = Path(FILES_DIR).resolve()

    # Find the src directory or use current working directory as base
    current_path = input_path
    src_base = None
    depth = 0
    while current_path.parent != current_path and depth < MAX_DIRECTORY_TRAVERSAL_DEPTH:
        if current_path.name == "src":
            src_base = current_path
            break
        current_path = current_path.parent
        depth += 1

    if src_base is None:
        # If no 'src' directory found, use the directory containing the input as base
        if input_path.parent.name == "src":
            src_base = input_path.parent
        else:
            # Fallback: find a reasonable base directory
            working_dir = Path.cwd()
            src_base = working_dir / "src" if (working_dir / "src").exists() else working_dir

    # Calculate the relative path from src_base to the input directory
    try:
        relative_from_src = input_path.relative_to(src_base)
        path_parts = relative_from_src.parts

        # Try to find a meaningful subset
        meaningful_part = None
        for _i, part in enumerate(path_parts):
            if part in [
                "autoverus",
                "clover",
                "synthesis_task",
                "first_8",
                "atomizer_supported",
                "atomizer_supported_tasks_dep_only",
                "numpy_specs",
                "DafnySpecs",
                "benchmarks",
            ]:
                meaningful_part = Path(part)
                break

        if meaningful_part is None:
            # If no recognized pattern, use the last 1-2 directory levels
            if len(path_parts) >= 2:
                meaningful_part = Path(path_parts[-2]) / Path(path_parts[-1])
            else:
                meaningful_part = Path(path_parts[-1]) if path_parts else Path("specs")

    except ValueError:
        # input_path is not relative to src_base, use the basename
        meaningful_part = Path(input_path.name)

    # Create output directory structure
    OUTPUT_DIR = str(
        src_base / f"code_from_spec_on_{timestamp}" / CURRENT_LANGUAGE / meaningful_part
    )
    SUMMARY_FILE = str(Path(OUTPUT_DIR) / "summary.txt")

    Path(OUTPUT_DIR).mkdir(parents=True, exist_ok=True)
    print(f"Created output directory: {OUTPUT_DIR}")

    # Use command-line arguments (with defaults)
    MAX_ITERATIONS = args.iterations
    DEBUG_MODE = args.debug
    STRICT_SPEC_VERIFICATION = args.strict_specs
    MAX_WORKERS = args.workers

    print("\nConfiguration:")
    print(f"- Language: {LANGUAGE_CONFIG.name}")
    print(f"- Directory: {FILES_DIR}")
    print(f"- Output directory: {OUTPUT_DIR}")
    print(f"- Max iterations: {MAX_ITERATIONS}")
    print(f"- Parallel workers: {MAX_WORKERS}")
    print(f"- Tool path: {get_tool_path()}")
    print(f"- Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print(f"- Spec preservation: {'Strict' if STRICT_SPEC_VERIFICATION else 'Relaxed (default)'}")
    print("\nProceeding with configuration...")


def get_tool_path():
    """Get the tool path for the current language."""
    # First, try to find the tool in the system PATH
    tool_name = LANGUAGE_CONFIG.default_tool_path
    system_tool_path = shutil.which(tool_name)

    if system_tool_path:
        return system_tool_path

    # If not found in PATH, fall back to environment variable or default
    tool_path = os.getenv(LANGUAGE_CONFIG.tool_path_env, LANGUAGE_CONFIG.default_tool_path)
    if tool_path.startswith("~/"):
        tool_path = str(Path(tool_path).expanduser())
    return tool_path


def find_spec_files(directory):
    """Find specification files for the current language."""
    try:
        files = []
        for root, _dirs, filenames in os.walk(directory):
            for f in filenames:
                if f.endswith(LANGUAGE_CONFIG.file_extension):
                    file_path = str(Path(root) / f)
                    # For Lean, check if file contains 'sorry'
                    if CURRENT_LANGUAGE == "lean":
                        with Path(file_path).open() as file:
                            for line in file:
                                if "sorry" in line:
                                    files.append(file_path)
                                    break
                    else:
                        files.append(file_path)
        return files
    except Exception as e:
        print(f"Error reading directory {directory}: {e}")
        return []


def thread_safe_print(*args, **kwargs):
    """Thread-safe print function."""
    with print_lock:
        print(*args, **kwargs)


def call_claude_api(prompt):
    """Call Claude API with the given prompt."""
    if not ANTHROPIC_API_KEY:
        raise ValueError("ANTHROPIC_API_KEY environment variable is required")

    # Add rate limiting delay to avoid overwhelming the API
    time.sleep(API_RATE_LIMIT_DELAY)

    url = "https://api.anthropic.com/v1/messages"
    headers = {
        "Content-Type": "application/json",
        "x-api-key": ANTHROPIC_API_KEY,
        "anthropic-version": "2023-06-01",
    }
    payload = {
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 8192,
        "messages": [{"role": "user", "content": prompt}],
    }

    response = requests.post(url, headers=headers, json=payload, timeout=60)
    response.raise_for_status()
    data = response.json()

    # Extract text from the response
    if "content" in data and len(data["content"]) > 0:
        content = data["content"][0]
        if "text" in content:
            return content["text"]
        else:
            return str(content)
    else:
        raise ValueError("Unexpected response format from Claude API")


def extract_code(output):
    """Extract code from LLM response based on current language."""
    # First try to extract from code blocks
    for pattern in LANGUAGE_CONFIG.code_block_patterns:
        code_block_match = re.search(rf"```{pattern}\n(.*?)```", output, re.DOTALL | re.IGNORECASE)
        if code_block_match:
            code = code_block_match.group(1).strip()
            code = fix_incomplete_code(code)
            return code

    # Generic code block
    code_block_match = re.search(r"```\n(.*?)```", output, re.DOTALL)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(code)
        return code

    # If no code block, try to find language-specific code patterns
    lines = output.split("\n")
    code_lines = []
    in_code = False

    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (
            line.strip().startswith("Looking at")
            or line.strip().startswith("The errors show that:")
            or line.strip().startswith("The issue is in")
            or line.strip().startswith("This function will be")
            or line.strip().startswith("Below is a")
            or line.strip().startswith("Theo note:")
            or line.strip().startswith("// This function will be")
            or line.strip().startswith("// Below is a")
            or line.strip().startswith("// Theo note:")
            or line.strip().startswith("```")
            or re.match(r"^\d+\.", line.strip())
        ):
            continue

        # Start collecting when we see language keywords
        for keyword in LANGUAGE_CONFIG.keywords:
            if keyword in line:
                in_code = True
                break

        if in_code:
            code_lines.append(line)

    if code_lines:
        code = "\n".join(code_lines).strip()
        code = fix_incomplete_code(code)
        return code

    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(code)
    return code


def fix_incomplete_code(code):
    """Fix common incomplete code patterns based on language."""
    if CURRENT_LANGUAGE == "verus":
        return fix_incomplete_verus_code(code)
    elif CURRENT_LANGUAGE == "dafny":
        return fix_incomplete_dafny_code(code)
    elif CURRENT_LANGUAGE == "lean":
        return fix_incomplete_lean_code(code)
    return code


def fix_incomplete_verus_code(code):
    """Fix incomplete Verus code patterns."""
    lines = code.split("\n")
    fixed_lines = []
    in_verus_block = False

    for i, line in enumerate(lines):
        # Track verus! block
        if "verus!" in line:
            in_verus_block = True
        elif line.strip() == "} // verus!" or (line.strip() == "}" and in_verus_block):
            in_verus_block = False

        # Fix incomplete function bodies (non-spec functions)
        if (
            (line.strip().startswith("fn ") or line.strip().startswith("proof fn "))
            and "{" not in line
            and not line.strip().endswith(";")
        ):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if (
                    "{" in lines[j]
                    or lines[j].strip().startswith("unimplemented!")
                    or lines[j].strip().startswith("return")
                ):
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("fn ")
                    or lines[j].strip().startswith("spec fn")
                    or lines[j].strip().startswith("proof fn")
                ):
                    break
            if not has_body:
                # Add empty body with TODO comment
                fixed_lines.append(line)
                fixed_lines.append("{")
                fixed_lines.append(
                    "    return false;  // TODO: Remove this line and implement the function body"
                )
                fixed_lines.append("}")
                continue

        # Fix incomplete spec function bodies
        if (
            line.strip().startswith("spec fn ")
            and "{" not in line
            and not line.strip().endswith(";")
        ):
            # Look ahead to see if there's a function body
            has_body = False
            for j in range(i + 1, len(lines)):
                if "{" in lines[j] or lines[j].strip() == ";":
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("fn ")
                    or lines[j].strip().startswith("spec fn")
                    or lines[j].strip().startswith("proof fn")
                ):
                    break
            if not has_body:
                # Add semicolon for spec functions without body
                fixed_lines.append(line + ";")
                continue

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


def fix_incomplete_dafny_code(code):
    """Fix incomplete Dafny code patterns."""
    lines = code.split("\n")
    fixed_lines = []

    for _i, line in enumerate(lines):
        # Fix incomplete strings in Dafny
        if ':= "' in line and not line.strip().endswith('"'):
            line = line.rstrip() + '""' if line.strip().endswith(':= "') else line.rstrip() + '"'

        # Fix incomplete variable declarations
        if "var " in line and " := " in line and not line.endswith(";"):
            if not line.strip().endswith("}"):
                line = line.rstrip() + ";"

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


def fix_incomplete_lean_code(code):
    """Fix incomplete Lean code patterns."""
    lines = code.split("\n")
    fixed_lines = []

    for i, line in enumerate(lines):
        # Fix incomplete sorry statements
        if "sorry" not in line and (
            line.strip().startswith("theorem ")
            or line.strip().startswith("lemma ")
            or line.strip().startswith("def ")
        ):
            # Look ahead to see if there's a body
            has_body = False
            for j in range(i + 1, len(lines)):
                if ":=" in lines[j] or "sorry" in lines[j] or "where" in lines[j]:
                    has_body = True
                    break
                if (
                    lines[j].strip().startswith("theorem ")
                    or lines[j].strip().startswith("lemma ")
                    or lines[j].strip().startswith("def ")
                ):
                    break
            if not has_body and ":" in line:
                # Add sorry for incomplete theorems/lemmas
                fixed_lines.append(line)
                fixed_lines.append("  sorry")
                continue

        fixed_lines.append(line)

    return "\n".join(fixed_lines)


def detect_compilation_errors(output):
    """Detect if the output contains compilation errors."""
    return any(indicator in output.lower() for indicator in COMMON_COMPILATION_ERRORS)


def check_tool_availability():
    """Check if the language tool is available at the specified path."""
    tool_path = get_tool_path()
    try:
        # Check if the tool executable exists
        if not Path(tool_path).is_file():
            return ToolAvailabilityResult(
                False, f"{LANGUAGE_CONFIG.name} executable not found at: {tool_path}"
            )

        # Check if the file is executable
        if not os.access(tool_path, os.X_OK):
            return ToolAvailabilityResult(
                False, f"{LANGUAGE_CONFIG.name} executable is not executable: {tool_path}"
            )

        # Try to run tool with --help to verify it works
        result = subprocess.run([tool_path, "--help"], capture_output=True, text=True, timeout=10)

        if result.returncode != 0 and CURRENT_LANGUAGE != "lean":
            # Lean might not have --help, so we skip this check for Lean
            return ToolAvailabilityResult(
                False, f"{LANGUAGE_CONFIG.name} executable failed to run: {result.stderr}"
            )

        return ToolAvailabilityResult(True, f"{LANGUAGE_CONFIG.name} is available and working")

    except subprocess.TimeoutExpired:
        return ToolAvailabilityResult(
            False, f"{LANGUAGE_CONFIG.name} executable timed out when checking availability"
        )
    except Exception as e:
        return ToolAvailabilityResult(
            False, f"Error checking {LANGUAGE_CONFIG.name} availability: {str(e)}"
        )


def verify_file(file_path):
    """Verify a file and return the result."""
    tool_path = get_tool_path()
    try:
        # First try compilation check if available
        if LANGUAGE_CONFIG.compile_check_command:
            cmd = [
                part.format(tool_path=tool_path, file_path=file_path)
                for part in LANGUAGE_CONFIG.compile_check_command
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            if result.returncode != 0:
                # Compilation failed
                full_output = result.stdout + result.stderr
                return VerificationResult(
                    success=False, output=full_output, error=f"Compilation failed: {full_output}"
                )

        # Try verification
        cmd = [
            part.format(tool_path=tool_path, file_path=file_path)
            for part in LANGUAGE_CONFIG.verify_command
        ]
        timeout_value = getattr(
            LANGUAGE_CONFIG, "timeout", 120
        )  # Default to 120 seconds if not specified
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_value)
        full_output = result.stdout + result.stderr

        # Check for success indicators
        success = result.returncode == 0
        for indicator in LANGUAGE_CONFIG.success_indicators:
            if indicator in full_output:
                success = True
                break

        if success:
            return VerificationResult(success=True, output=full_output, error=None)
        else:
            return VerificationResult(
                success=False, output=full_output, error=f"Verification failed: {full_output}"
            )

    except subprocess.TimeoutExpired:
        return VerificationResult(success=False, output="", error="Verification timeout")
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))


def save_iteration_code(relative_path, iteration, code, phase):
    """Save code after each iteration for debugging."""
    if not DEBUG_MODE:
        return

    base_name = Path(relative_path).stem

    if phase in ["original", "generated", "current"]:
        iteration_file_name = (
            f"{base_name}_iter_{iteration}_{phase}{LANGUAGE_CONFIG.file_extension}"
        )

        relative_dir = str(Path(relative_path).parent)
        output_subdir = str(Path(OUTPUT_DIR) / relative_dir) if relative_dir != "." else OUTPUT_DIR

        with file_write_lock:
            Path(output_subdir).mkdir(parents=True, exist_ok=True)
            iteration_path = Path(output_subdir) / iteration_file_name
            with iteration_path.open("w") as f:
                f.write(code)

        thread_safe_print(f"    💾 Saved {phase} code to: {iteration_file_name}")


def verify_spec_preservation(original_code, generated_code):
    """Verify that all specifications from the original code are preserved in the generated code."""
    if not STRICT_SPEC_VERIFICATION:
        return True

    for pattern in LANGUAGE_CONFIG.spec_patterns:
        original_specs = re.findall(pattern, original_code, re.DOTALL)

        for spec in original_specs:
            spec_content = spec.strip()

            # Normalize whitespace for comparison
            normalized_spec = re.sub(r"\s+", " ", spec_content)
            normalized_generated = re.sub(r"\s+", " ", generated_code)

            # Check if the normalized content is present
            if normalized_spec not in normalized_generated:
                thread_safe_print(
                    f"    ⚠️  Specification missing or modified: {spec_content[:100]}..."
                )
                return False

    return True


def restore_specs(original_code, generated_code):
    """Restore original specifications in the generated code."""
    # This is a simplified version - you may need to customize for each language
    # For now, we'll just prepend the original specs
    result = []

    # Extract all specs from original
    all_specs = []
    for pattern in LANGUAGE_CONFIG.spec_patterns:
        specs = re.findall(f"({pattern})", original_code, re.DOTALL)
        all_specs.extend(specs)

    if all_specs:
        # Add original specs at the beginning
        for spec in all_specs:
            result.append(spec[0].strip())
            result.append("")

        # Add generated code
        result.append(generated_code)
        return "\n".join(result)

    return generated_code


def process_spec_file(file_path):
    """Process a single specification file."""
    try:
        thread_safe_print(f"Processing: {Path(file_path).name}")

        # Read the original file
        with Path(file_path).open() as f:
            original_code = f.read()

        # Calculate relative path from input directory to preserve hierarchy
        relative_path = os.path.relpath(file_path, FILES_DIR)
        base_file_name = Path(file_path).stem

        # Save original code
        save_iteration_code(relative_path, 0, original_code, "original")

        # Check if original file has compilation errors
        thread_safe_print("  Checking original file for compilation errors...")
        original_verification = verify_file(file_path)

        if not original_verification.success:
            thread_safe_print(f"  ⚠️  Original file has issues: {original_verification.error}")
            thread_safe_print("  Will attempt to fix during processing...")

        # Step 1: Generate code from specifications
        thread_safe_print("  Step 1: Generating code from specifications...")
        try:
            generate_prompt = prompt_loader.format_prompt("generate_code", code=original_code)
        except KeyError as e:
            thread_safe_print(f"  ✗ Prompt error: {e}")
            thread_safe_print(f"  Available prompts: {list(prompt_loader.prompts.keys())}")
            raise
        except Exception as e:
            thread_safe_print(f"  ✗ Error formatting prompt: {e}")
            raise

        generated_response = call_claude_api(generate_prompt)
        generated_code = extract_code(generated_response)

        # Verify that all specifications are preserved
        if STRICT_SPEC_VERIFICATION and not verify_spec_preservation(original_code, generated_code):
            thread_safe_print(
                "  ⚠️  Warning: Specifications were modified. Restoring original specifications..."
            )
            generated_code = restore_specs(original_code, generated_code)

        # Save initial generated code
        save_iteration_code(relative_path, 1, generated_code, "generated")

        # Create output file path preserving directory structure
        relative_dir = str(Path(relative_path).parent)
        output_subdir = str(Path(OUTPUT_DIR) / relative_dir) if relative_dir != "." else OUTPUT_DIR

        # Thread-safe directory creation
        with file_write_lock:
            Path(output_subdir).mkdir(parents=True, exist_ok=True)

        output_path = str(
            Path(output_subdir) / f"{base_file_name}_impl{LANGUAGE_CONFIG.file_extension}"
        )
        with Path(output_path).open("w") as f:
            f.write(generated_code)

        # Run verification iterations
        current_code = generated_code
        success = False
        last_verification = None

        for iteration in range(1, MAX_ITERATIONS + 1):
            thread_safe_print(f"  Iteration {iteration}/{MAX_ITERATIONS}: Verifying...")

            # Write current code to file
            with Path(output_path).open("w") as f:
                f.write(current_code)

            # Save current working version for this iteration
            save_iteration_code(relative_path, iteration, current_code, "current")

            # Verify
            verification = verify_file(output_path)
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
            if iteration < MAX_ITERATIONS:
                thread_safe_print("    Attempting to fix errors...")
                fix_prompt = prompt_loader.format_prompt(
                    "fix_verification",
                    code=current_code,
                    errorDetails=error_details,
                    iteration=iteration,
                )

                try:
                    fix_response = call_claude_api(fix_prompt)
                    fixed_code = extract_code(fix_response)

                    # Verify that all specifications are still preserved
                    if STRICT_SPEC_VERIFICATION and not verify_spec_preservation(
                        original_code, fixed_code
                    ):
                        thread_safe_print(
                            "    ⚠️  Warning: Specifications were modified during fix. Restoring original specifications..."
                        )
                        fixed_code = restore_specs(original_code, fixed_code)

                    current_code = fixed_code
                    thread_safe_print(f"    Generated fix for iteration {iteration}")
                except Exception as e:
                    thread_safe_print(f"    ✗ Failed to generate fix: {str(e)}")
                    break

        if success:
            thread_safe_print(f"  ✓ Successfully generated and verified: {Path(output_path).name}")
            return ProcessingResult(
                success=True, file=relative_path, output=output_path, error=None, has_bypass=False
            )
        else:
            error_msg = (
                last_verification.error if last_verification else "Unknown verification error"
            )
            thread_safe_print(
                f"  ✗ Failed to verify after {MAX_ITERATIONS} iterations: {error_msg[:200] if error_msg else 'Unknown error'}..."
            )
            return ProcessingResult(
                success=False,
                file=relative_path,
                output=output_path,
                error=error_msg,
                has_bypass=False,
            )

    except Exception as e:
        thread_safe_print(f"✗ Failed: {Path(file_path).name} - {str(e)}")
        return ProcessingResult(
            success=False,
            file=relative_path if "relative_path" in locals() else Path(file_path).name,
            error=str(e),
            output=None,
            has_bypass=False,
        )


def get_git_remote_url():
    """Get the GitHub remote URL from git configuration."""
    try:
        result = subprocess.run(
            ["git", "config", "--get", "remote.origin.url"],
            capture_output=True,
            text=True,
            check=True,
        )
        remote_url = result.stdout.strip()
        if remote_url.startswith("git@github.com:"):
            remote_url = remote_url.replace("git@github.com:", "https://github.com/").replace(
                ".git", ""
            )
        elif remote_url.startswith("https://github.com/"):
            remote_url = remote_url.replace(".git", "")
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
        return remote_url
    except subprocess.CalledProcessError:
        print("Error: Could not get git remote URL. Make sure you're in a git repository.")
        return None
    except Exception as e:
        print(f"Error getting git remote URL: {e}")
        return None


def get_current_branch():
    """Get the current git branch."""
    try:
        result = subprocess.run(
            ["git", "branch", "--show-current"], capture_output=True, text=True, check=True
        )
        return result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        try:
            result = subprocess.run(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout.strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            return "main"


def get_github_url(file_path, repo_url, branch="main"):
    repo_url = repo_url.rstrip("/")
    encoded_path = quote(str(file_path))
    github_url = f"{repo_url}/blob/{branch}/{encoded_path}"
    return github_url


def get_repo_root():
    """Find the repository root by looking for .git directory."""
    current = Path.cwd()
    while current != current.parent:
        if (current / ".git").exists():
            return current
        current = current.parent
    return Path.cwd()  # Fallback to current directory


def generate_csv_results(results):
    """Generate CSV file with spec_name, spec_to_code, spec_link, and impl_link columns."""
    csv_file = str(Path(OUTPUT_DIR) / "results.csv")

    # Get repo info
    repo_url = get_git_remote_url() or ""
    branch = get_current_branch() or "main"
    repo_root = get_repo_root()

    with Path(csv_file).open("w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(["spec_name", "spec_to_code", "spec_link", "impl_link"])
        # Write results
        for result in results:
            spec_name = Path(result.file).stem  # Remove extension and preserve path
            spec_to_code = "SUCCESS" if result.success else "FAILED"

            # Generate spec link
            spec_full_path = str(Path(FILES_DIR) / result.file)
            spec_rel_path = os.path.relpath(spec_full_path, repo_root)
            spec_link = get_github_url(spec_rel_path, repo_url, branch) if repo_url else ""

            # Generate impl link
            if result.output:
                impl_rel_path = os.path.relpath(result.output, repo_root)
                impl_link = get_github_url(impl_rel_path, repo_url, branch) if repo_url else ""
            else:
                impl_link = ""

            writer.writerow([spec_name, spec_to_code, spec_link, impl_link])

    print(f"CSV results saved to: {csv_file}")
    return csv_file


def generate_summary(results):
    """Generate a summary of the processing results."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success]

    summary_lines = [
        f"=== {LANGUAGE_CONFIG.name.upper()} SPECIFICATION-TO-CODE PROCESSING SUMMARY (PARALLEL VERSION) ===",
        "",
        f"Language: {LANGUAGE_CONFIG.name}",
        f"Test directory: {FILES_DIR}",
        f"Output directory: {OUTPUT_DIR}",
        f"Max iterations: {MAX_ITERATIONS}",
        f"Parallel workers: {MAX_WORKERS}",
        f"Test date: {datetime.now().isoformat()}",
        "",
        f"Total original files: {len(results)}",
        "",
        "=== OVERALL STATISTICS ===",
        f"Total successful: {len(successful)}",
        f"Total failed: {len(failed)}",
        f"Success rate: {(len(successful) / len(results) * 100) if results else 0.0:.1f}%",
        "",
        "=== SUCCESSFUL FILES (VERIFIED) ===",
    ]

    for result in successful:
        output_file = Path(result.output).name if result.output else "no output"
        summary_lines.append(f"✓ {result.file} -> {output_file}")

    summary_lines.extend(
        [
            "",
            "=== FAILED FILES (VERIFICATION) ===",
        ]
    )

    summary_lines.extend([f"✗ {result.file}" for result in failed])

    summary_lines.extend(
        [
            "",
            "=== PARALLEL PROCESSING FEATURES ===",
            f"Parallel workers: {MAX_WORKERS}",
            f"API rate limiting: {API_RATE_LIMIT_DELAY}s between calls",
            f"Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}",
        ]
    )

    if DEBUG_MODE:
        summary_lines.extend(
            [
                "- Saves original specification as *_iter_0_original"
                + LANGUAGE_CONFIG.file_extension,
                "- Saves initial generated code as *_iter_1_generated"
                + LANGUAGE_CONFIG.file_extension,
                "- Saves current working version for each iteration as *_iter_N_current"
                + LANGUAGE_CONFIG.file_extension,
                "- Saves final implementation as *_impl" + LANGUAGE_CONFIG.file_extension,
                "- Full debugging: all intermediate files are saved",
            ]
        )
    else:
        summary_lines.extend(
            [
                "- Saves only final implementation as *_impl" + LANGUAGE_CONFIG.file_extension,
                "- No intermediate files saved (debug mode disabled)",
            ]
        )

    summary_lines.extend(
        [
            "",
            f"- Debug mode control: {'Enabled' if DEBUG_MODE else 'Disabled'}",
            "- Configurable file output based on debug setting",
            "",
            f"Generated on: {datetime.now().isoformat()}",
        ]
    )

    summary = "\n".join(summary_lines)

    with Path(SUMMARY_FILE).open("w") as f:
        f.write(summary)

    return summary


def process_files_parallel(spec_files):
    """Process files in parallel using ThreadPoolExecutor."""
    results = []
    completed_count = 0
    total_files = len(spec_files)

    print(f"Processing {total_files} files using {MAX_WORKERS} parallel workers...")
    print("")

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        # Submit all tasks
        future_to_file = {
            executor.submit(process_spec_file, file_path): file_path for file_path in spec_files
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
                relative_path = os.path.relpath(file_path, FILES_DIR)
                error_result = ProcessingResult(
                    success=False,
                    file=relative_path,
                    error=f"Unexpected error: {str(e)}",
                    output=None,
                    has_bypass=False,
                )
                results.append(error_result)
                thread_safe_print(
                    f"[{completed_count}/{total_files}] ✗ {Path(file_path).name} - Unexpected error: {str(e)}"
                )

    return results


def main():
    global prompt_loader

    # Parse command-line arguments first
    args = parse_arguments()

    # Set up configuration
    setup_configuration(args)

    # Initialize prompt loader for the selected language
    try:
        prompt_loader = PromptLoader(prompts_file=LANGUAGE_CONFIG.prompts_file)
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation.valid:
            print(f"Warning: Missing required prompts: {', '.join(validation.missing)}")
            print(f"Available prompts: {', '.join(validation.available)}")
            sys.exit(1)
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print(
            f"Please ensure the {LANGUAGE_CONFIG.prompts_file} file exists in the {CURRENT_LANGUAGE} directory."
        )
        print("Expected locations:")
        script_dir = Path(__file__).parent
        print(f"  - {script_dir / CURRENT_LANGUAGE / LANGUAGE_CONFIG.prompts_file}")
        print(f"  - {LANGUAGE_CONFIG.prompts_file} (current directory)")
        sys.exit(1)

    print(
        f"Starting specification-to-code processing of {LANGUAGE_CONFIG.name} files (PARALLEL VERSION)..."
    )
    print(f"Directory: {FILES_DIR}")
    print(f"Output directory: {OUTPUT_DIR}")
    print(f"Tool path: {get_tool_path()}")
    print(f"Max iterations: {MAX_ITERATIONS}")
    print(f"Parallel workers: {MAX_WORKERS}")
    print(f"Debug mode: {'Enabled' if DEBUG_MODE else 'Disabled'}")
    print(f"- Spec preservation: {'Strict' if STRICT_SPEC_VERIFICATION else 'Relaxed (default)'}")
    print("Processing each file by generating code from specifications.")
    if DEBUG_MODE:
        print("DEBUG MODE: Saves code after each iteration to separate files for analysis.")
    else:
        print("NORMAL MODE: Saves only final implementation files.")
    print("")

    if not ANTHROPIC_API_KEY:
        print("Error: ANTHROPIC_API_KEY environment variable is required")
        print('Please set it with: export ANTHROPIC_API_KEY="your-api-key"')
        sys.exit(1)

    # Check if tool is available before proceeding
    print(f"Checking {LANGUAGE_CONFIG.name} availability...")
    tool_availability = check_tool_availability()
    if not tool_availability.available:
        print(f"Error: {tool_availability.message}")
        print(
            f"Please ensure {LANGUAGE_CONFIG.name} is installed and the {LANGUAGE_CONFIG.tool_path_env} environment variable is set correctly."
        )
        print(f"Current {LANGUAGE_CONFIG.tool_path_env}: {get_tool_path()}")
        print(
            f"You can set it with: export {LANGUAGE_CONFIG.tool_path_env}=/path/to/{CURRENT_LANGUAGE}"
        )
        sys.exit(1)

    print(f"✓ {tool_availability.message}")
    print("")

    # Find all specification files
    spec_files = find_spec_files(FILES_DIR)
    print(f"Found {len(spec_files)} {LANGUAGE_CONFIG.name} files to process")
    if CURRENT_LANGUAGE == "lean":
        print("(Only Lean files containing 'sorry' are selected)")
    print("")

    if not spec_files:
        print(f"No {LANGUAGE_CONFIG.name} files found. Exiting.")
        return

    # Process files in parallel
    start_time = time.time()
    results = process_files_parallel(spec_files)
    end_time = time.time()
    processing_time = end_time - start_time

    # Generate summary
    print("")
    print("Generating summary...")
    summary = generate_summary(results)

    print("")
    print("=== SUMMARY ===")
    print(summary)
    print("")
    print(f"Summary saved to: {SUMMARY_FILE}")
    print(f"All generated files saved to: {OUTPUT_DIR}")
    print(f"Total processing time: {processing_time:.2f} seconds")
    print(f"Average time per file: {processing_time / len(results):.2f} seconds")
    if DEBUG_MODE:
        print(
            "DEBUG: Files saved: original, generated, current per iteration, and final implementation"
        )
    else:
        print("NORMAL: Only final implementation files saved")

    # Generate CSV results
    generate_csv_results(results)

    # Print final statistics
    successful = [r for r in results if r.success]
    print(
        f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({len(successful) / len(results) * 100:.1f}%)"
    )
    print(f"⚡ Parallel processing with {MAX_WORKERS} workers completed in {processing_time:.2f}s")


if __name__ == "__main__":
    main()
