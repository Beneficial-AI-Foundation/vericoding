from pathlib import Path
from vericoding.common.prompt_loader import BasePromptLoader


class PromptLoader(BasePromptLoader):
    """Dafny-specific prompt loader."""
    
    def _get_default_prompts_file(self) -> Path:
        """Get the default prompts file path for Dafny."""
        # Point to the original dafny/prompts.yaml location
        return Path(__file__).parent.parent.parent.parent / "dafny" / "prompts.yaml"
    
    def _get_required_prompts(self) -> list:
        """Get the list of required prompts for Dafny."""
        return [
            "generate_code",
            "fix_verification"
        ]