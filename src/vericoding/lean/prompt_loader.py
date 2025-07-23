from pathlib import Path
from vericoding.common.prompt_loader import BasePromptLoader


class PromptLoader(BasePromptLoader):
    """Lean-specific prompt loader."""
    
    def _get_default_prompts_file(self) -> Path:
        """Get the default prompts file path for Lean."""
        # Point to the original lean-vc/prompts-lean.yaml location
        return Path(__file__).parent.parent.parent.parent / "lean-vc" / "prompts-lean.yaml"
    
    def _get_required_prompts(self) -> list:
        """Get the list of required prompts for Lean."""
        return [
            "generate_code",
            "fix_verification"
        ]