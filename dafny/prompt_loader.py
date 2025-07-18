import os
import yaml
from pathlib import Path

class PromptLoader:
    """Utility class to load prompts from a YAML file."""
    
    def __init__(self, prompts_file=None):
        """Initialize the prompt loader.
        
        Args:
            prompts_file: Path to the YAML file containing prompts. If None, uses default location.
        """
        if prompts_file is None:
            # Default to prompts.yaml relative to this file
            self.prompts_file = Path(__file__).parent / "prompts.yaml"
        else:
            self.prompts_file = Path(prompts_file)
        
        if not self.prompts_file.exists():
            raise FileNotFoundError(f"Prompts file not found: {self.prompts_file}")
        
        # Load all prompts at initialization
        self._load_prompts()
    
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
        required_prompts = [
            "generate_code",
            "fix_verification"
        ]
        
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