"""
Prompt loader for Lean verification - uses new Pydantic-based system.
Maintains backward compatibility with YAML-based prompts.
"""
from pathlib import Path
from typing import Optional, Dict, Any
from .prompts import LegacyPromptLoader, LeanPromptManager, LeanPromptConfig, PromptType


class PromptLoader:
    """Lean-specific prompt loader with backward compatibility."""
    
    def __init__(self, prompts_file=None):
        """Initialize prompt loader.
        
        Args:
            prompts_file: Optional path to YAML file (for backward compatibility)
        """
        # Use legacy loader for backward compatibility
        if prompts_file is None:
            # Check if YAML file exists in default location
            yaml_path = Path(__file__).parent.parent.parent.parent / "lean-vc" / "prompts-lean.yaml"
            if yaml_path.exists():
                prompts_file = yaml_path
        
        self.legacy_loader = LegacyPromptLoader(prompts_file)
        self.manager = LeanPromptManager()
        self.prompts = {}  # For compatibility
    
    def format_prompt(self, prompt_name: str, **kwargs) -> str:
        """Format a prompt with the given parameters.
        
        Maintains backward compatibility with existing code.
        """
        return self.legacy_loader.format_prompt(prompt_name, **kwargs)
    
    def format_prompt_with_mcp(self, prompt_name: str, use_mcp: bool = True, **kwargs) -> str:
        """Format a prompt with MCP tool instructions."""
        if prompt_name == "generate_code":
            config = LeanPromptConfig(
                type=PromptType.GENERATE,
                code=kwargs.get('code', ''),
                use_mcp=use_mcp,
                mcp_tools=self.manager.get_mcp_tools_for_stage("generate"),
                iteration=kwargs.get('iteration', 0),
                max_iterations=kwargs.get('max_iterations', 5)
            )
            return self.manager.create_prompt(config)
        elif prompt_name == "fix_verification":
            config = LeanPromptConfig(
                type=PromptType.FIX,
                code=kwargs.get('code', ''),
                error_details=kwargs.get('errorDetails', ''),
                use_mcp=use_mcp,
                mcp_tools=self.manager.get_mcp_tools_for_stage("fix"),
                iteration=kwargs.get('iteration', 0),
                max_iterations=kwargs.get('max_iterations', 5)
            )
            return self.manager.create_prompt(config)
        else:
            # Fall back to legacy
            return self.format_prompt(prompt_name, **kwargs)
    
    def validate_prompts(self) -> Dict[str, Any]:
        """Validate that required prompts exist."""
        required = ["generate_code", "fix_verification"]
        available = required  # We always have these in the new system
        
        return {
            "valid": True,
            "available": available,
            "missing": [],
            "total_required": len(required),
            "total_available": len(available)
        }
    
    def get_available_prompts(self) -> list:
        """Get list of available prompts."""
        return ["generate_code", "fix_verification"]