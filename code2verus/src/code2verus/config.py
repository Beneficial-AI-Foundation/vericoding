from pathlib import Path
import yaml


def load_config() -> dict:
    """Load configuration from config.yml"""
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


_cfg = load_config()
cfg = _cfg.get("config", {})
system_prompt = _cfg.get("system", "")

# Make the full config available for accessing sections like yaml_instructions
full_cfg = _cfg

ARTIFACTS = Path(cfg.get("artifacts_dir", "artifacts"))
ARTIFACTS.mkdir(parents=True, exist_ok=True)


def get_config_value(
    key: str, default: int | None = None, required: bool = True
) -> int:
    """Get a configuration value with validation.

    Args:
        key: The configuration key to retrieve
        default: Default value if key is not found (only used when required=False)
        required: Whether the configuration key is required

    Returns:
        The configuration value as an integer

    Raises:
        ValueError: If the key is required but not found, or if the value is not a positive integer
    """
    value = cfg.get(key, default)

    if value is None:
        if required:
            raise ValueError(f"{key} must be configured in config.yml")
        # This should never happen if default is provided and required=False
        raise ValueError(
            f"Invalid configuration: {key} is None and no valid default provided"
        )

    # Ensure value is a valid positive integer
    if not isinstance(value, int) or value <= 0:
        raise ValueError(f"{key} must be a positive integer, got: {value}")

    return value


def get_error_template(template_name: str, **kwargs) -> str:
    """Get an error template with formatted variables.

    Args:
        template_name: The name of the error template to retrieve
        **kwargs: Template variables to format into the template

    Returns:
        The formatted error template string

    Raises:
        KeyError: If the template name is not found
    """
    error_templates = full_cfg.get("error_templates", {})

    if template_name not in error_templates:
        raise KeyError(f"Error template '{template_name}' not found in config")

    template = error_templates[template_name]
    return template.format(**kwargs)
