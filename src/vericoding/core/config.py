"""Configuration management for vericoding."""

from dataclasses import dataclass
from pathlib import Path
import tomllib


# Load environment variables from .env file
def load_environment():
    """Load environment variables from .env file if it exists."""
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


@dataclass
class LanguageConfig:
    """Configuration for a specific programming language."""

    name: str
    file_extension: str  # e.g., ".dfy", ".py", ".rs"
    tool_path_env: str  # Environment variable name
    default_tool_path: str | Path  # Path to the language tool
    prompts_file: str | Path  # Path to prompts file
    verify_command: list[str]  # Command and arguments for verification
    compile_check_command: list[str] | None  # Optional compilation check
    code_block_patterns: list[str]  # Regex patterns for code blocks
    keywords: list[str]  # Language-specific keywords
    spec_patterns: list[str]  # Patterns for specification blocks


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
    max_workers: int
    api_rate_limit_delay: int
    llm: str
    max_directory_traversal_depth: int = 50
    assume_unformatted_lean: bool = False
    unit_test: bool = False

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
    """Load language configuration from TOML file."""
    # Try to find config file relative to this module's location
    module_dir = Path(__file__).parent.parent.parent  # Go up to the repository root
    config_path = module_dir / "config" / "language_config.toml"

    if not config_path.exists():
        # Fallback to current directory
        config_path = Path("config/language_config.toml")
        if not config_path.exists():
            config_path = Path("language_config.toml")  # Final fallback

    if not config_path.exists():
        raise FileNotFoundError(f"Language configuration file not found: {config_path}")

    try:
        # tomllib.load() requires a binary file object (opened with "rb"), not text mode.
        # This is different from most config parsers (like configparser or json), which accept text mode ("r").
        # If you use text mode here, tomllib.load() will raise a TypeError because it expects bytes, not str.
        # Do not change to "r".
        with config_path.open("rb") as f:
            config_data = tomllib.load(f)
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
        common_compilation_errors = config_data.get("common_compilation_errors", [])
        if not common_compilation_errors and "common" in config_data:
            common_compilation_errors = config_data["common"].get(
                "common_compilation_errors", []
            )

        # Process each language (the keys in the root of the TOML file)
        for lang_name, lang_data in config_data.items():
            # Skip non-language entries
            if lang_name in ["common_compilation_errors", "common"]:
                continue
            if not isinstance(lang_data, dict):
                continue

            languages[lang_name] = LanguageConfig(**lang_data)

        return LanguageConfigResult(
            languages=languages, common_compilation_errors=common_compilation_errors
        )
    except KeyError as e:
        raise ValueError(
            f"Missing required configuration key in {config_path}: {e}"
        ) from e
    except Exception as e:
        raise ValueError(
            f"Error processing configuration from {config_path}: {e}"
        ) from e
