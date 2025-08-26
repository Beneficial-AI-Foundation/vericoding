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

    def __init__(self, language: str, prompts_file: str = "prompts.yaml") -> None:
        self.language = language
        self.prompts_file = prompts_file
        self.prompts: dict[str, str] = {}
        self._load_prompts()

    def _load_prompts(self) -> None:
        """Load prompts from YAML file."""
        # Get the script directory
        script_dir = Path(__file__).parent.parent.parent

        # First try in the language-specific directory relative to script
        lang_prompts_path = script_dir / self.language / self.prompts_file
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
        required = ["generate_code", "fix_verification"]
        missing = [p for p in required if p not in self.prompts]
        return PromptValidationResult(
            valid=len(missing) == 0,
            missing=missing,
            available=list(self.prompts.keys()),
        )


def init_prompt_loader(language: str, prompts_file: str) -> PromptLoader:
    """Initialize and validate a prompt loader for the given language."""
    try:
        prompt_loader = PromptLoader(language, prompts_file=prompts_file)
        
        # Validate prompts on startup
        validation = prompt_loader.validate_prompts()
        if not validation.valid:
            print(f"Warning: Missing required prompts: {', '.join(validation.missing)}")
            print(f"Available prompts: {', '.join(validation.available)}")
            sys.exit(1)
            
        return prompt_loader
        
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print(f"Please ensure the {prompts_file} file exists in the {language} directory.")
        print("Expected locations:")
        script_dir = Path(__file__).parent.parent.parent
        print(f"  - {script_dir / language / prompts_file}")
        print(f"  - {prompts_file} (current directory)")
        sys.exit(1)



