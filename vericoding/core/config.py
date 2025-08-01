"""Configuration management for vericoding."""

from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml


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


@dataclass
class LanguageConfig:
    """Configuration for a specific programming language."""

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
class LanguageConfigResult:
    """Result of loading language configuration."""

    languages: dict[str, LanguageConfig]
    common_compilation_errors: list[str]


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
    max_directory_traversal_depth: int = 50

    # Static configuration loaded once
    _static_config: LanguageConfigResult | None = None

    @classmethod
    def _get_static_config(cls) -> LanguageConfigResult:
        """Get or load static configuration."""
        if cls._static_config is None:
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


def load_language_config() -> LanguageConfigResult:
    """Load language configuration from YAML file."""
    # Try to find config file relative to this module's location
    module_dir = Path(__file__).parent.parent.parent  # Go up to the repository root
    config_path = module_dir / "config" / "language_config.yaml"

    if not config_path.exists():
        # Fallback to current directory
        config_path = Path("config/language_config.yaml")
        if not config_path.exists():
            config_path = Path("language_config.yaml")  # Final fallback

    if not config_path.exists():
        raise FileNotFoundError(f"Language configuration file not found: {config_path}")

    with open(config_path, "r") as f:
        config_data = yaml.safe_load(f)

    languages = {}
    # Extract common compilation errors if they exist
    common_compilation_errors = config_data.get("common_compilation_errors", [])

    # Process each language (the keys in the root of the YAML file)
    for lang_name, lang_data in config_data.items():
        # Skip non-language entries
        if lang_name in ["common_compilation_errors"]:
            continue
        if not isinstance(lang_data, dict):
            continue

        languages[lang_name] = LanguageConfig.from_dict(lang_data)

    return LanguageConfigResult(
        languages=languages, common_compilation_errors=common_compilation_errors
    )
