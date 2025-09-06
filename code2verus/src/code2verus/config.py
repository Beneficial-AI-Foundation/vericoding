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

ARTIFACTS = Path(cfg.get("artifacts_dir", "artifacts"))
ARTIFACTS.mkdir(parents=True, exist_ok=True)
