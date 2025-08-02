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
import anthropic
from abc import ABC, abstractmethod

try:
    import tomllib  # Python 3.11+
except ImportError:
    try:
        import tomli as tomllib  # Fallback for older Python versions
    except ImportError as e:
        raise ImportError(
            "TOML support requires Python 3.11+ or the 'tomli' package. "
            "Install with: pip install tomli"
        ) from e
import yaml

# Module-level thread safety locks (need to be shared across all instances)
_print_lock = threading.Lock()
_file_write_lock = threading.Lock()


# Load environment variables from .env file
def load_environment():
    """Load environment variables from .env file if it exists."""
    try:
        from dotenv import load_dotenv

        # Look for .env file in current directory and parent directories
        env_file = Path(".env")
        if not env_file.exists():
            # Try parent directory (useful when running from subdirectories)
            env_file = Path("../.env")

        if env_file.exists():
            load_dotenv(env_file)
            print(f"✓ Loaded environment variables from {env_file}")
        else:
            # Try to load from default location
            load_dotenv()
    except ImportError:
        # Fallback if dotenv is not installed
        print(
            "Note: python-dotenv not installed. Using system environment variables only."
        )
        print("To use .env files, install with: pip install python-dotenv")
    except Exception as e:
        print(f"Warning: Could not load .env file: {e}")


# Initialize environment loading
load_environment()


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
    config_path = Path(__file__).parent / "config" / "language_config.toml"
    if not config_path.exists():
        # Fallback to looking in current directory
        config_path = Path("language_config.toml")

    if not config_path.exists():
        raise FileNotFoundError(f"Language configuration file not found: {config_path}")

    try:
        # tomllib.load() requires a binary file object, not text mode.
        # This differs from most config parsers; do not change to "r".
        with config_path.open("rb") as f:
            config = tomllib.load(f)
    except (OSError, IOError) as e:
        raise FileNotFoundError(
            f"Could not read configuration file {config_path}: {e}"
        ) from e
    except Exception as e:
        raise ValueError(
            f"Invalid TOML syntax in configuration file {config_path}: {e}"
        ) from e

    try:
        languages = {}
        # Extract common compilation errors - check both root level and common section
        common_compilation_errors = config.get("common_compilation_errors", [])
        if not common_compilation_errors and "common" in config:
            common_compilation_errors = config["common"].get(
                "common_compilation_errors", []
            )

        # Process each language (the keys in the root of the TOML file)
        for lang, settings in config.items():
            # Skip non-language entries
            if lang in ["common_compilation_errors", "common"]:
                continue
            if not isinstance(settings, dict):
                continue
            languages[lang] = LanguageConfig.from_dict(settings)

        return LanguageConfigResult(
            languages=languages,
            common_compilation_errors=common_compilation_errors,
        )
    except KeyError as e:
        raise ValueError(
            f"Missing required configuration key in {config_path}: {e}"
        ) from e
    except Exception as e:
        raise ValueError(
            f"Error processing configuration from {config_path}: {e}"
        ) from e


# Abstract LLM Interface
class LLMProvider(ABC):
    """Abstract interface for LLM providers."""

    def __init__(
        self, api_key: str, model: str, max_tokens: int = 8192, timeout: float = 60.0
    ):
        self.api_key = api_key
        self.model = model
        self.max_tokens = max_tokens
        self.timeout = timeout

    @abstractmethod
    def call_api(self, prompt: str) -> str:
        """Call the LLM API with the given prompt."""
        pass

    @abstractmethod
    def get_required_env_var(self) -> str:
        """Return the required environment variable name for API key."""
        pass


class AnthropicProvider(LLMProvider):
    """Anthropic Claude LLM provider."""

    def __init__(
        self, api_key: str, model: str = "claude-3-5-sonnet-20241022", **kwargs
    ):
        super().__init__(api_key, model, **kwargs)
        self.client = anthropic.Anthropic(api_key=api_key)

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                messages=[{"role": "user", "content": prompt}],
                timeout=self.timeout,
            )

            if response.content and len(response.content) > 0:
                text_content = response.content[0]
                if hasattr(text_content, "text"):
                    return text_content.text
                else:
                    return str(text_content)
            else:
                raise ValueError("Unexpected response format from Claude API")

        except anthropic.APIError as e:
            raise ValueError(f"Anthropic API error: {str(e)}")
        except Exception as e:
            raise ValueError(f"Error calling Claude API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "ANTHROPIC_API_KEY"


class OpenAIProvider(LLMProvider):
    """OpenAI GPT LLM provider."""

    def __init__(self, api_key: str, model: str = "gpt-4o", **kwargs):
        super().__init__(api_key, model, **kwargs)
        try:
            import openai

            self.client = openai.OpenAI(api_key=api_key)
        except ImportError:
            raise ImportError(
                "OpenAI package not installed. Install with: pip install openai"
            )

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                return response.choices[0].message.content
            else:
                raise ValueError("Unexpected response format from OpenAI API")

        except Exception as e:
            raise ValueError(f"Error calling OpenAI API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "OPENAI_API_KEY"


class DeepSeekProvider(LLMProvider):
    """DeepSeek LLM provider."""

    def __init__(self, api_key: str, model: str = "deepseek-chat", **kwargs):
        super().__init__(api_key, model, **kwargs)
        try:
            import openai  # DeepSeek uses OpenAI-compatible API

            self.client = openai.OpenAI(
                api_key=api_key, base_url="https://api.deepseek.com"
            )
        except ImportError:
            raise ImportError(
                "OpenAI package not installed. Install with: pip install openai"
            )

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                return response.choices[0].message.content
            else:
                raise ValueError("Unexpected response format from DeepSeek API")

        except Exception as e:
            raise ValueError(f"Error calling DeepSeek API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "DEEPSEEK_API_KEY"


def create_llm_provider(provider_name: str, model: str = None) -> LLMProvider:
    """Factory function to create LLM providers."""
    provider_configs = {
        "claude": {
            "class": AnthropicProvider,
            "default_model": "claude-3-5-sonnet-20241022",
            "env_var": "ANTHROPIC_API_KEY",
        },
        "openai": {
            "class": OpenAIProvider,
            "default_model": "gpt-4o",
            "env_var": "OPENAI_API_KEY",
        },
        "deepseek": {
            "class": DeepSeekProvider,
            "default_model": "deepseek-chat",
            "env_var": "DEEPSEEK_API_KEY",
        },
    }

    if provider_name not in provider_configs:
        available = ", ".join(provider_configs.keys())
        raise ValueError(
            f"Unsupported LLM provider: {provider_name}. Available: {available}"
        )

    config = provider_configs[provider_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var)

    if not api_key:
        raise ValueError(
            f"{env_var} environment variable is required for {provider_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key"
        )

    selected_model = model or config["default_model"]
    return config["class"](api_key, selected_model)


@dataclass
class ProcessingConfig:
    """Configuration for the specification-to-code processing."""

    language: str
    language_config: LanguageConfig
    files_dir: str
    max_iterations: int
    output_dir: str
    summary_file: str
    debug_mode: bool
    strict_spec_verification: bool
    max_workers: int
    api_rate_limit_delay: int
    llm_provider: str
    llm_model: str | None
    max_directory_traversal_depth: int = (
        50  # Maximum depth to prevent excessive directory traversal
    )

    # Static configuration loaded once
    @classmethod
    def _get_static_config(cls) -> LanguageConfigResult:
        """Load static language configuration (called once per module load)."""
        if not hasattr(cls, "_static_config"):
            cls._static_config = load_language_config()
        return cls._static_config

    @classmethod
    def get_available_languages(cls) -> dict[str, LanguageConfig]:
        """Get available languages."""
        return cls._get_static_config().languages

    @classmethod
    def get_common_compilation_errors(cls) -> list[str]:
        """Get common compilation errors."""
        return cls._get_static_config().common_compilation_errors


class PromptLoader:
    def __init__(
        self, config: ProcessingConfig, prompts_file: str = "prompts.yaml"
    ) -> None:
        self.config = config
        self.prompts_file: str = prompts_file
        self.prompts: dict[str, str] = {}
        self._load_prompts()

    def _load_prompts(self) -> None:
        # Get the script directory
        script_dir = Path(__file__).parent

        # First try in the language-specific directory relative to script
        lang_prompts_path = script_dir / self.config.language / self.prompts_file
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
            valid=len(missing) == 0,
            missing=missing,
            available=list(self.prompts.keys()),
        )


def parse_arguments():
    """Parse command-line arguments."""
    # Get available languages for argument choices
    available_languages = ProcessingConfig.get_available_languages()

    parser = argparse.ArgumentParser(
        description="Unified Specification-to-Code Processing",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Supported languages: {", ".join(available_languages.keys())}
Supported LLM providers: claude, openai, deepseek

Examples:
  python spec_to_code.py dafny ./specs
  python spec_to_code.py lean ./NumpySpec/DafnySpecs --iterations 3
  python spec_to_code.py verus ./benchmarks/verus_specs --debug --iterations 5
  python spec_to_code.py dafny ./specs --workers 8 --iterations 3 --llm-provider openai
  python spec_to_code.py verus ./specs --workers 2 --debug --llm-provider deepseek --llm-model deepseek-chat
  python spec_to_code.py dafny ./specs --llm-provider claude --llm-model claude-3-5-sonnet-20241022
        """,
    )

    parser.add_argument(
        "language",
        type=str,
        choices=list(available_languages.keys()),
        help="Programming language to process",
    )

    parser.add_argument("folder", type=Path, help="Directory with specification files")

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


def setup_configuration(args) -> ProcessingConfig:
    """Set up processing configuration from command line arguments."""
    available_languages = ProcessingConfig.get_available_languages()
    language_config = available_languages[args.language]

    print(
        f"=== {language_config.name} Specification-to-Code Processing Configuration ===\n"
    )

    files_dir = str(args.folder)

    if not Path(files_dir).is_dir():
        print(f"Error: Directory '{files_dir}' does not exist or is not accessible.")
        sys.exit(1)

    # Create timestamped output directory outside the input directory
    timestamp = datetime.now().strftime("%d-%m_%Hh%M")

    # Extract the relevant part of the input path for the output hierarchy
    input_path = Path(files_dir).resolve()

    # Find the src directory or use current working directory as base
    current_path = input_path
    src_base = None
    depth = 0
    while (
        current_path.parent != current_path
        and depth < args.max_directory_traversal_depth
    ):
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
            src_base = (
                working_dir / "src" if (working_dir / "src").exists() else working_dir
            )

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
    output_dir = str(
        src_base / f"code_from_spec_on_{timestamp}" / args.language / meaningful_part
    )
    summary_file = str(Path(output_dir) / "summary.txt")

    Path(output_dir).mkdir(parents=True, exist_ok=True)
    print(f"Created output directory: {output_dir}")

    # Create configuration object
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
    print(
        f"- Spec preservation: {'Strict' if config.strict_spec_verification else 'Relaxed (default)'}"
    )
    print(f"- API rate limit delay: {config.api_rate_limit_delay}s")
    print("\nProceeding with configuration...")

    return config


def get_tool_path(config: ProcessingConfig):
    """Get the tool path for the current language."""
    # First, try to find the tool in the system PATH
    tool_name = config.language_config.default_tool_path
    system_tool_path = shutil.which(tool_name)

    if system_tool_path:
        return system_tool_path

    # If not found in PATH, fall back to environment variable or default
    tool_path = os.getenv(
        config.language_config.tool_path_env, config.language_config.default_tool_path
    )
    if tool_path.startswith("~/"):
        tool_path = str(Path(tool_path).expanduser())
    return tool_path


def find_spec_files(config: ProcessingConfig):
    """Find specification files for the current language."""
    try:
        files = []
        for root, _dirs, filenames in os.walk(config.files_dir):
            for f in filenames:
                if f.endswith(config.language_config.file_extension):
                    file_path = str(Path(root) / f)
                    # For Lean, check if file contains 'sorry'
                    if config.language == "lean":
                        with Path(file_path).open() as file:
                            for line in file:
                                if "sorry" in line:
                                    files.append(file_path)
                                    break
                    else:
                        files.append(file_path)
        return files
    except Exception as e:
        print(f"Error reading directory {config.files_dir}: {e}")
        return []


def thread_safe_print(*args, **kwargs):
    """Thread-safe print function."""
    with _print_lock:
        print(*args, **kwargs)


def call_llm_api(config: ProcessingConfig, prompt):
    """Call LLM API with the given prompt using the configured provider."""
    # Add rate limiting delay to avoid overwhelming the API
    time.sleep(config.api_rate_limit_delay)

    # Create the LLM provider
    try:
        llm_provider = create_llm_provider(config.llm_provider, config.llm_model)
        return llm_provider.call_api(prompt)
    except Exception as e:
        raise ValueError(f"Error calling {config.llm_provider} API: {str(e)}")


def extract_code(config: ProcessingConfig, output):
    """Extract code from LLM response based on current language."""
    # First try to extract from code blocks
    for pattern in config.language_config.code_block_patterns:
        code_block_match = re.search(
            rf"```{pattern}\n(.*?)```", output, re.DOTALL | re.IGNORECASE
        )
        if code_block_match:
            code = code_block_match.group(1).strip()
            code = fix_incomplete_code(config, code)
            return code

    # Generic code block
    code_block_match = re.search(r"```\n(.*?)```", output, re.DOTALL)
    if code_block_match:
        code = code_block_match.group(1).strip()
        code = fix_incomplete_code(config, code)
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
        for keyword in config.language_config.keywords:
            if keyword in line:
                in_code = True
                break

        if in_code:
            code_lines.append(line)

    if code_lines:
        code = "\n".join(code_lines).strip()
        code = fix_incomplete_code(config, code)
        return code

    # Fallback: return the original output but cleaned
    code = output.strip()
    code = fix_incomplete_code(config, code)
    return code


def fix_incomplete_code(config: ProcessingConfig, code):
    """Fix common incomplete code patterns based on language."""
    if config.language == "verus":
        return fix_incomplete_verus_code(code)
    elif config.language == "dafny":
        return fix_incomplete_dafny_code(code)
    elif config.language == "lean":
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
            line = (
                line.rstrip() + '""'
                if line.strip().endswith(':= "')
                else line.rstrip() + '"'
            )

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


def detect_compilation_errors(config: ProcessingConfig, output):
    """Detect if the output contains compilation errors."""
    common_errors = config.get_common_compilation_errors()
    return any(indicator in output.lower() for indicator in common_errors)


def check_tool_availability(config: ProcessingConfig):
    """Check if the language tool is available at the specified path."""
    tool_path = get_tool_path(config)
    try:
        # Check if the tool executable exists
        if not Path(tool_path).is_file():
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable not found at: {tool_path}",
            )

        # Check if the file is executable
        if not os.access(tool_path, os.X_OK):
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable is not executable: {tool_path}",
            )

        # Try to run tool with --help to verify it works
        result = subprocess.run(
            [tool_path, "--help"], capture_output=True, text=True, timeout=10
        )

        if result.returncode != 0 and config.language != "lean":
            # Lean might not have --help, so we skip this check for Lean
            return ToolAvailabilityResult(
                False,
                f"{config.language_config.name} executable failed to run: {result.stderr}",
            )

        return ToolAvailabilityResult(
            True, f"{config.language_config.name} is available and working"
        )

    except subprocess.TimeoutExpired:
        return ToolAvailabilityResult(
            False,
            f"{config.language_config.name} executable timed out when checking availability",
        )
    except Exception as e:
        return ToolAvailabilityResult(
            False,
            f"Error checking {config.language_config.name} availability: {str(e)}",
        )


def verify_file(config: ProcessingConfig, file_path):
    """Verify a file and return the result."""
    tool_path = get_tool_path(config)
    try:
        # First try compilation check if available
        if config.language_config.compile_check_command:
            cmd = [
                part.format(tool_path=tool_path, file_path=file_path)
                for part in config.language_config.compile_check_command
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)

            if result.returncode != 0:
                # Compilation failed
                full_output = result.stdout + result.stderr
                return VerificationResult(
                    success=False,
                    output=full_output,
                    error=f"Compilation failed: {full_output}",
                )

        # Try verification
        cmd = [
            part.format(tool_path=tool_path, file_path=file_path)
            for part in config.language_config.verify_command
        ]
        timeout_value = getattr(
            config.language_config, "timeout", 120
        )  # Default to 120 seconds if not specified
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_value
        )
        full_output = result.stdout + result.stderr

        # Check for success indicators
        success = result.returncode == 0
        for indicator in config.language_config.success_indicators:
            if indicator in full_output:
                success = True
                break

        if success:
            return VerificationResult(success=True, output=full_output, error=None)
        else:
            return VerificationResult(
                success=False,
                output=full_output,
                error=f"Verification failed: {full_output}",
            )

    except subprocess.TimeoutExpired:
        return VerificationResult(
            success=False, output="", error="Verification timeout"
        )
    except Exception as e:
        return VerificationResult(success=False, output="", error=str(e))


def save_iteration_code(
    config: ProcessingConfig, relative_path, iteration, code, phase
):
    """Save code after each iteration for debugging."""
    if not config.debug_mode:
        return

    base_name = Path(relative_path).stem

    if phase in ["original", "generated", "current"]:
        iteration_file_name = f"{base_name}_iter_{iteration}_{phase}{config.language_config.file_extension}"

        relative_dir = Path(relative_path).parent
        output_subdir = (
            Path(config.output_dir) / relative_dir
            if str(relative_dir) != "."
            else Path(config.output_dir)
        )

        with _file_write_lock:
            output_subdir.mkdir(parents=True, exist_ok=True)
            iteration_path = output_subdir / iteration_file_name
            with iteration_path.open("w") as f:
                f.write(code)

        thread_safe_print(f"    💾 Saved {phase} code to: {iteration_file_name}")


def verify_spec_preservation(config: ProcessingConfig, original_code, generated_code):
    """Verify that all specifications from the original code are preserved in the generated code."""
    if not config.strict_spec_verification:
        return True

    for pattern in config.language_config.spec_patterns:
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


def restore_specs(config: ProcessingConfig, original_code, generated_code):
    """Restore original specifications in the generated code."""
    # This is a simplified version - you may need to customize for each language
    # For now, we'll just prepend the original specs
    result = []

    # Extract all specs from original
    all_specs = []
    for pattern in config.language_config.spec_patterns:
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


def process_spec_file(config: ProcessingConfig, prompt_loader: PromptLoader, file_path):
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
        relative_dir = Path(relative_path).parent
        output_subdir = (
            Path(config.output_dir) / relative_dir
            if str(relative_dir) != "."
            else Path(config.output_dir)
        )

        # Thread-safe directory creation
        with _file_write_lock:
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
            verification = verify_file(config, output_path)
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
            remote_url = remote_url.replace(
                "git@github.com:", "https://github.com/"
            ).replace(".git", "")
        elif remote_url.startswith("https://github.com/"):
            remote_url = remote_url.replace(".git", "")
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
        return remote_url
    except subprocess.CalledProcessError:
        print(
            "Error: Could not get git remote URL. Make sure you're in a git repository."
        )
        return None
    except Exception as e:
        print(f"Error getting git remote URL: {e}")
        return None


def get_current_branch():
    """Get the current git branch."""
    try:
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            capture_output=True,
            text=True,
            check=True,
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


def generate_csv_results(config: ProcessingConfig, results):
    """Generate CSV file with spec_name, spec_to_code, spec_link, and impl_link columns."""
    csv_file = Path(config.output_dir) / "results.csv"

    # Get repo info
    repo_url = get_git_remote_url() or ""
    branch = get_current_branch() or "main"
    repo_root = get_repo_root()

    with csv_file.open("w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        # Write header
        writer.writerow(["spec_name", "spec_to_code", "spec_link", "impl_link"])
        # Write results
        for result in results:
            spec_name = Path(result.file).stem  # Remove extension and preserve path
            spec_to_code = "SUCCESS" if result.success else "FAILED"

            # Generate spec link
            spec_full_path = Path(config.files_dir) / result.file
            spec_rel_path = spec_full_path.relative_to(Path(repo_root))
            spec_link = (
                get_github_url(spec_rel_path, repo_url, branch) if repo_url else ""
            )

            # Generate impl link
            if result.output:
                impl_rel_path = Path(result.output).relative_to(Path(repo_root))
                impl_link = (
                    get_github_url(impl_rel_path, repo_url, branch) if repo_url else ""
                )
            else:
                impl_link = ""

            writer.writerow([spec_name, spec_to_code, spec_link, impl_link])

    print(f"CSV results saved to: {csv_file}")
    return str(csv_file)


def generate_summary(config: ProcessingConfig, results):
    """Generate a summary of the processing results."""
    successful = [r for r in results if r.success]
    failed = [r for r in results if not r.success]

    summary_lines = [
        f"=== {config.language_config.name.upper()} SPECIFICATION-TO-CODE PROCESSING SUMMARY (PARALLEL VERSION) ===",
        "",
        f"Language: {config.language_config.name}",
        f"Test directory: {config.files_dir}",
        f"Output directory: {config.output_dir}",
        f"Max iterations: {config.max_iterations}",
        f"Parallel workers: {config.max_workers}",
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
            f"Parallel workers: {config.max_workers}",
            f"API rate limiting: {config.api_rate_limit_delay}s between calls",
            f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}",
        ]
    )

    if config.debug_mode:
        summary_lines.extend(
            [
                "- Saves original specification as *_iter_0_original"
                + config.language_config.file_extension,
                "- Saves initial generated code as *_iter_1_generated"
                + config.language_config.file_extension,
                "- Saves current working version for each iteration as *_iter_N_current"
                + config.language_config.file_extension,
                "- Saves final implementation as *_impl"
                + config.language_config.file_extension,
                "- Full debugging: all intermediate files are saved",
            ]
        )
    else:
        summary_lines.extend(
            [
                "- Saves only final implementation as *_impl"
                + config.language_config.file_extension,
                "- No intermediate files saved (debug mode disabled)",
            ]
        )

    summary_lines.extend(
        [
            "",
            f"- Debug mode control: {'Enabled' if config.debug_mode else 'Disabled'}",
            "- Configurable file output based on debug setting",
            "",
            f"Generated on: {datetime.now().isoformat()}",
        ]
    )

    summary = "\n".join(summary_lines)

    with Path(config.summary_file).open("w") as f:
        f.write(summary)

    return summary


def process_files_parallel(
    config: ProcessingConfig, prompt_loader: PromptLoader, spec_files
):
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


def main():
    # Parse command-line arguments first
    args = parse_arguments()

    # Set up configuration
    config = setup_configuration(args)

    # Initialize prompt loader for the selected language
    try:
        prompt_loader = PromptLoader(
            config, prompts_file=config.language_config.prompts_file
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
        f"Starting specification-to-code processing of {config.language_config.name} files (PARALLEL VERSION)..."
    )
    print(f"Directory: {config.files_dir}")
    print(f"Output directory: {config.output_dir}")
    print(f"Tool path: {get_tool_path(config)}")
    print(f"Max iterations: {config.max_iterations}")
    print(f"Parallel workers: {config.max_workers}")
    print(f"Debug mode: {'Enabled' if config.debug_mode else 'Disabled'}")
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

    # Process files in parallel
    start_time = time.time()
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
    print(f"Average time per file: {processing_time / len(results):.2f} seconds")
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
    print(
        f"\n🎉 Processing completed: {len(successful)}/{len(results)} files successful ({len(successful) / len(results) * 100:.1f}%)"
    )
    print(
        f"⚡ Parallel processing with {config.max_workers} workers completed in {processing_time:.2f}s"
    )


if __name__ == "__main__":
    main()
