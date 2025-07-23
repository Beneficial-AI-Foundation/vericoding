"""Base prompt loader class for all verification tools."""
import os
import yaml
from pathlib import Path
from abc import ABC, abstractmethod


class BasePromptLoader(ABC):
    """Base class for loading prompts from YAML files."""
    
    def __init__(self, prompts_file=None):
        """Initialize the prompt loader.
        
        Args:
            prompts_file: Path to the YAML file containing prompts.
        """
        self.prompts_file = Path(prompts_file) if prompts_file else self._get_default_prompts_file()
        
        if not self.prompts_file.exists():
            raise FileNotFoundError(f"Prompts file not found: {self.prompts_file}")
        
        # Load all prompts at initialization
        self._load_prompts()
    
    @abstractmethod
    def _get_default_prompts_file(self) -> Path:
        """Get the default prompts file path for the specific tool."""
        pass
    
    def _load_prompts(self):
        """Load all prompts from the YAML file."""
        try:
            with open(self.prompts_file, 'r', encoding='utf-8') as f:
                self.prompts = yaml.safe_load(f)
        except yaml.YAMLError as e:
            raise ValueError(f"Error parsing YAML file {self.prompts_file}: {e}")
    
    def load_prompt(self, prompt_name):
        """Load a specific prompt by name.
        
        Args:
            prompt_name: Name of the prompt to load
            
        Returns:
            str: The prompt content
            
        Raises:
            KeyError: If the prompt name doesn't exist
        """
        if prompt_name not in self.prompts:
            raise KeyError(f"Prompt '{prompt_name}' not found in {self.prompts_file}")
        
        return self.prompts[prompt_name]
    
    def get_available_prompts(self):
        """Get a list of available prompt names.
        
        Returns:
            list: List of prompt names
        """
        return list(self.prompts.keys())
    
    def format_prompt(self, prompt_name, **kwargs):
        """Load a prompt and format it with the given parameters.
        
        Args:
            prompt_name: Name of the prompt to load
            **kwargs: Parameters to format into the prompt
            
        Returns:
            str: The formatted prompt
        """
        prompt_template = self.load_prompt(prompt_name)
        return prompt_template.format(**kwargs)
    
    def validate_prompts(self):
        """Validate that all required prompts exist.
        
        Returns:
            dict: Validation results with missing prompts listed
        """
        required_prompts = self._get_required_prompts()
        
        missing = []
        available = []
        
        for prompt in required_prompts:
            if prompt in self.prompts:
                available.append(prompt)
            else:
                missing.append(prompt)
        
        return {
            "valid": len(missing) == 0,
            "available": available,
            "missing": missing,
            "total_required": len(required_prompts),
            "total_available": len(available)
        }
    
    @abstractmethod
    def _get_required_prompts(self) -> list:
        """Get the list of required prompts for the specific tool."""
        pass
    
    def reload_prompts(self):
        """Reload prompts from the YAML file (useful for development)."""
        self._load_prompts()
    
    def get_prompt_info(self):
        """Get information about all loaded prompts.
        
        Returns:
            dict: Information about prompts including names and character counts
        """
        info = {}
        for name, content in self.prompts.items():
            info[name] = {
                "name": name,
                "length": len(content),
                "lines": len(content.split('\n')),
                "has_placeholders": '{' in content
            }
        return info
    
    def load_claude_md(self, claude_md_path=None):
        """Load CLAUDE.md file and return its content.
        
        Args:
            claude_md_path: Path to CLAUDE.md file. If None, looks for it in project root.
            
        Returns:
            str: Content of CLAUDE.md file, or empty string if not found
        """
        if claude_md_path is None:
            # Look for CLAUDE.md in project root (3 levels up from src/vericoding/common)
            claude_md_path = Path(__file__).parent.parent.parent.parent / "CLAUDE.md"
        
        if claude_md_path.exists():
            with open(claude_md_path, 'r', encoding='utf-8') as f:
                return f.read()
        return ""