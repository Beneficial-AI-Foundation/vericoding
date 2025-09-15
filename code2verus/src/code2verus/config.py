from pathlib import Path
import yaml
from typing import Dict, Any, Optional, Union


def load_config(config_path: Optional[Union[str, Path]] = None) -> dict:
    """Load configuration from config.yml or specified path"""
    if config_path is not None:
        config_path = Path(config_path)
        if config_path.exists():
            with open(config_path, "r") as f:
                return yaml.safe_load(f)
        else:
            raise FileNotFoundError(f"Config file not found: {config_path}")

    # Try to find config.yml in the current directory or the project root
    config_paths = [
        Path(".") / "config.yml",
        Path(__file__).parent.parent.parent / "config.yml",
    ]

    for config_path in config_paths:
        if config_path.exists():
            with open(config_path, "r") as f:
                return yaml.safe_load(f)

    raise FileNotFoundError("config.yml not found in current directory or project root")


def merge_configs(*configs: Dict[str, Any]) -> Dict[str, Any]:
    """Merge multiple configuration dictionaries, with later configs taking precedence."""
    result = {}

    for config in configs:
        for key, value in config.items():
            if (
                key in result
                and isinstance(result[key], dict)
                and isinstance(value, dict)
            ):
                # Recursively merge dictionaries
                result[key] = merge_configs(result[key], value)
            else:
                # Replace with new value
                result[key] = value

    return result


def load_translation_config(source_lang: str, target_lang: str = "verus") -> dict:
    """Load configuration for a specific language translation.

    Args:
        source_lang: Source language (e.g., 'dafny', 'lean', 'verus')
        target_lang: Target language (default: 'verus')

    Returns:
        Merged configuration with base config and translation-specific config
    """
    project_root = Path(__file__).parent.parent.parent
    config_dir = project_root / "config"

    # Load base configuration
    base_config_path = config_dir / "base.yml"
    if not base_config_path.exists():
        # Fallback to original config.yml if new structure doesn't exist
        return load_config()

    base_config = load_config(base_config_path)

    # Determine translation config file name
    if source_lang == "verus" and target_lang == "dafny":
        translation_file = "verus-to-dafny.yml"
    elif source_lang == "verus" and target_lang == "lean":
        translation_file = "verus-to-lean.yml"
    elif source_lang == "dafny" and target_lang == "verus":
        translation_file = "dafny-to-verus.yml"
    elif source_lang == "dafny" and target_lang == "lean":
        translation_file = "dafny-to-lean.yml"
    elif source_lang == "lean" and target_lang == "verus":
        translation_file = "lean-to-verus.yml"
    else:
        # If no specific translation config exists, just use base
        return base_config

    # Load translation-specific configuration
    translation_config_path = config_dir / translation_file
    if translation_config_path.exists():
        translation_config = load_config(translation_config_path)
        return merge_configs(base_config, translation_config)

    return base_config


_cfg = load_config()
cfg = _cfg.get("config", {})
system_prompt = _cfg.get("system", "")

# Make the full config available for accessing sections like yaml_instructions
full_cfg = _cfg

ARTIFACTS = Path(cfg.get("artifacts_dir", "artifacts"))
ARTIFACTS.mkdir(parents=True, exist_ok=True)


def get_config_value(
    key: str, default: int | None = None, required: bool = True
) -> int | None:
    """Get a configuration value with validation.

    Args:
        key: The configuration key to retrieve
        default: Default value if key is not found (only used when required=False)
        required: Whether the configuration key is required

    Returns:
        The configuration value as an integer, or None if not required and default is None

    Raises:
        ValueError: If the key is required but not found, or if the value is not a positive integer
    """
    value = cfg.get(key, default)

    if value is None:
        if required:
            raise ValueError(f"{key} must be configured in config.yml")
        # If not required and default was explicitly None, this is valid
        if default is None:
            return None
        # This should never happen if a non-None default is provided and required=False
        raise ValueError(
            f"Invalid configuration: {key} is None and no valid default provided"
        )

    # Ensure value is a valid positive integer
    if not isinstance(value, int) or value <= 0:
        raise ValueError(f"{key} must be a positive integer, got: {value}")

    return value


def get_error_template(
    template_name: str, source_lang: str = "dafny", target_lang: str = "verus", **kwargs
) -> str:
    """Get an error template with formatted variables.

    Args:
        template_name: The name of the error template to retrieve
        source_lang: Source language for translation-specific config
        target_lang: Target language for translation-specific config
        **kwargs: Template variables to format into the template

    Returns:
        The formatted error template string

    Raises:
        KeyError: If the template name is not found
    """
    # Use translation-specific config if available, fallback to global config
    try:
        translation_cfg = load_translation_config(source_lang, target_lang)
        error_templates = translation_cfg.get("error_templates", {})
    except FileNotFoundError:
        # Fallback to global config if translation-specific config doesn't exist
        error_templates = full_cfg.get("error_templates", {})

    if template_name not in error_templates:
        raise KeyError(f"Error template '{template_name}' not found in config")

    template = error_templates[template_name]
    return template.format(**kwargs)
