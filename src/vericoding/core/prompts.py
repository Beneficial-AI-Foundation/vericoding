"""Prompt loading and validation."""

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import yaml


@dataclass
class PromptValidationResult:
    """Result of prompt validation."""

    valid: bool
    missing: list[str]
    available: list[str]


class PromptLoader:
    """Handles loading and formatting of prompts for different languages."""

    def __init__(self, language: str, mode: str = "spec", prompts_file: str = None) -> None:
        self.language = language
        self.mode = mode
        self.prompts_file = prompts_file or f"prompts_{mode}.yaml"
        self.prompts: dict[str, str] = {}
        self._load_prompts()

    def _load_prompts(self) -> None:
        """Load prompts from YAML file."""
        # Get the project root directory (go up from src/vericoding/core to project root)
        project_root = Path(__file__).parent.parent.parent.parent

        # First try in the new prompts directory structure
        prompts_path = project_root / "src" / "prompts" / self.language / self.prompts_file
        if prompts_path.exists():
            with prompts_path.open() as f:
                self.prompts = yaml.safe_load(f)
            return

        # Fallback: try in the old language-specific directory relative to project root
        lang_prompts_path = project_root / self.language / self.prompts_file
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
        """Format a prompt with the given parameters."""
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
        """Validate that required prompts are available."""
        
        required_prompts = ["generate_code", "fix_verification"]
        missing = [p for p in required_prompts if p not in self.prompts]
        return PromptValidationResult(
            valid=len(missing) == 0,
            missing=missing,
            available=list(self.prompts.keys()),
        )


def init_prompt_loader(language: str, mode: str = "spec", prompts_file: str = None) -> PromptLoader:
    """Initialize and validate a prompt loader for the given language."""
    try:
        prompt_loader = PromptLoader(language, mode=mode, prompts_file=prompts_file)
        
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation.valid:
            print(f"Warning: Missing required prompts: {', '.join(validation.missing)}")
            print(f"Available prompts: {', '.join(validation.available)}")
            sys.exit(1)
            
        return prompt_loader
        
    except FileNotFoundError as e:
        print(f"Error: {e}")
        expected_file = prompts_file or f"prompts_{mode}.yaml"
        print(f"Please ensure the {expected_file} file exists in the prompts directory.")
        print("Expected locations:")
        project_root = Path(__file__).parent.parent.parent.parent
        print(f"  - {project_root / 'src' / 'prompts' / language / expected_file}")
        print(f"  - {project_root / language / expected_file}")
        print(f"  - {expected_file} (current directory)")
        sys.exit(1)



