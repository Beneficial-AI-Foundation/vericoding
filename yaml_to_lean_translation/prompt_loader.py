#!/usr/bin/env python3
"""
Prompt Loader for YAML to Lean Translation

This module handles loading and formatting prompts from the prompts.yaml file.
"""

import yaml
from pathlib import Path
from typing import Dict, Any

class PromptLoader:
    """Loads and manages prompts for YAML to Lean translation."""
    
    def __init__(self, prompts_file: str = "prompts.yaml"):
        self.prompts_file = Path(__file__).parent / prompts_file
        self.prompts = self._load_prompts()
        self.config = self.prompts.get('config', {})
    
    def _load_prompts(self) -> Dict[str, Any]:
        """Load prompts from the YAML file."""
        try:
            with open(self.prompts_file, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except Exception as e:
            print(f"Error loading prompts from {self.prompts_file}: {e}")
            return {}
    
    def get_translation_prompt(self, yaml_content: Dict, filename: str) -> str:
        """Get the formatted translation prompt."""
        if 'translation_prompt' not in self.prompts:
            raise ValueError("Translation prompt not found in prompts.yaml")
        
        # Extract components from YAML
        preamble = yaml_content.get('vc-preamble', '')
        helpers = yaml_content.get('vc-helpers', '')
        spec = yaml_content.get('vc-spec', '')
        code = yaml_content.get('vc-code', '')
        postamble = yaml_content.get('vc-postamble', '')
        
        # Clean filename for metadata
        filename_clean = filename.replace('.yaml', '')
        
        # Format the prompt template
        prompt_template = self.prompts['translation_prompt']
        formatted_prompt = prompt_template.format(
            filename=filename,
            filename_clean=filename_clean,
            preamble=preamble,
            helpers=helpers,
            spec=spec,
            code=code,
            postamble=postamble
        )
        
        return formatted_prompt
    
    def get_config(self) -> Dict[str, Any]:
        """Get the configuration settings."""
        return self.config.copy()
    
    def get_model(self) -> str:
        """Get the default model name."""
        return self.config.get('model', 'claude-3-5-sonnet-20241022')
    
    def get_max_tokens(self) -> int:
        """Get the maximum tokens setting."""
        return self.config.get('max_tokens', 4000)
    
    def get_temperature(self) -> float:
        """Get the temperature setting."""
        return self.config.get('temperature', 0.1)
    
    def get_max_retries(self) -> int:
        """Get the maximum retries setting."""
        return self.config.get('max_retries', 3)
    
    def get_rate_limit_delay(self) -> int:
        """Get the rate limit delay setting."""
        return self.config.get('rate_limit_delay', 1)
