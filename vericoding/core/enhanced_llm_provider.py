"""Enhanced LLM provider with automatic model selection and large context handling."""

import os
from typing import Optional, Dict, List, Tuple
from pathlib import Path

from .llm_providers import LLMProvider, create_llm_provider
from .context_window_config import (
    get_model_context_config,
    get_optimal_model_for_text,
    can_fit_in_context,
    estimate_token_count,
    get_models_with_large_context,
    ModelContextConfig,
)


class EnhancedLLMProvider:
    """Enhanced LLM provider with automatic model selection and context management."""
    
    def __init__(self, 
                 preferred_provider: str = "claude",
                 fallback_providers: Optional[List[str]] = None,
                 auto_model_selection: bool = True,
                 max_input_tokens: Optional[int] = None):
        """
        Initialize enhanced LLM provider.
        
        Args:
            preferred_provider: Primary provider to use
            fallback_providers: List of fallback providers if primary fails
            auto_model_selection: Whether to automatically select optimal model
            max_input_tokens: Maximum input tokens to use (None for auto)
        """
        self.preferred_provider = preferred_provider
        self.fallback_providers = fallback_providers or ["openai", "deepseek"]
        self.auto_model_selection = auto_model_selection
        self.max_input_tokens = max_input_tokens
        
        # Cache for provider instances
        self._provider_cache: Dict[str, LLMProvider] = {}
        
        # Track usage for optimization
        self._usage_stats: Dict[str, int] = {}
    
    def _get_provider(self, provider_name: str, model: Optional[str] = None) -> LLMProvider:
        """Get or create a provider instance."""
        cache_key = f"{provider_name}:{model}"
        if cache_key not in self._provider_cache:
            self._provider_cache[cache_key] = create_llm_provider(provider_name, model)
        return self._provider_cache[cache_key]
    
    def _select_optimal_model(self, input_text: str, output_tokens: int = 8192) -> Tuple[str, str]:
        """Select the optimal provider and model for the given input."""
        if not self.auto_model_selection:
            # Use preferred provider with default model
            return self.preferred_provider, None
        
        # Try to find optimal model starting with preferred provider
        optimal_model = get_optimal_model_for_text(
            input_text, output_tokens, self.preferred_provider
        )
        
        if optimal_model:
            # Determine provider from model name
            if optimal_model.startswith("claude"):
                return "claude", optimal_model
            elif optimal_model.startswith("gpt"):
                return "openai", optimal_model
            elif optimal_model.startswith("deepseek"):
                return "deepseek", optimal_model
        
        # Fallback to preferred provider with default model
        return self.preferred_provider, None
    
    def call_api_with_context_optimization(self, 
                                         prompt: str, 
                                         max_output_tokens: int = 8192,
                                         force_provider: Optional[str] = None,
                                         force_model: Optional[str] = None) -> str:
        """
        Call API with automatic context optimization.
        
        Args:
            prompt: The input prompt
            max_output_tokens: Maximum output tokens expected
            force_provider: Force specific provider
            force_model: Force specific model
            
        Returns:
            API response
        """
        # Select provider and model
        if force_provider and force_model:
            provider_name = force_provider
            model_name = force_model
        elif force_provider:
            provider_name = force_provider
            model_name = None
        else:
            provider_name, model_name = self._select_optimal_model(prompt, max_output_tokens)
        
        # Get provider instance
        provider = self._get_provider(provider_name, model_name)
        
        # Update usage stats
        self._usage_stats[provider.model] = self._usage_stats.get(provider.model, 0) + 1
        
        # Call API
        try:
            return provider.call_api(prompt)
        except Exception as e:
            # Try fallback providers if available
            if not force_provider and self.fallback_providers:
                for fallback_provider in self.fallback_providers:
                    if fallback_provider != provider_name:
                        try:
                            fallback = self._get_provider(fallback_provider)
                            self._usage_stats[fallback.model] = self._usage_stats.get(fallback.model, 0) + 1
                            return fallback.call_api(prompt)
                        except Exception:
                            continue
            
            # Re-raise original exception if all fallbacks fail
            raise e
    
    def process_large_codebase(self, 
                             codebase_path: str,
                             prompt_template: str,
                             max_output_tokens: int = 8192) -> str:
        """
        Process a large codebase by intelligently selecting relevant files.
        
        Args:
            codebase_path: Path to the codebase directory
            prompt_template: Template prompt with {codebase_content} placeholder
            max_output_tokens: Maximum output tokens expected
            
        Returns:
            API response
        """
        codebase_path = Path(codebase_path)
        
        # Get large context models
        large_context_models = get_models_with_large_context(500_000)
        
        if not large_context_models:
            raise ValueError("No models with large context windows available")
        
        # Select the model with the largest context window
        best_model = max(large_context_models.keys(), 
                        key=lambda m: large_context_models[m].input_tokens)
        model_config = large_context_models[best_model]
        
        # Collect relevant files
        relevant_files = self._collect_relevant_files(codebase_path)
        
        # Build codebase content
        codebase_content = self._build_codebase_content(relevant_files, model_config)
        
        # Create final prompt
        final_prompt = prompt_template.format(codebase_content=codebase_content)
        
        # Call API with the large context model
        return self.call_api_with_context_optimization(
            final_prompt, 
            max_output_tokens,
            force_model=best_model
        )
    
    def _collect_relevant_files(self, codebase_path: Path) -> List[Path]:
        """Collect relevant files from the codebase."""
        relevant_files = []
        
        # File extensions to include
        code_extensions = {'.py', '.lean', '.dfy', '.rs', '.java', '.cpp', '.c', '.h', '.hpp', '.cs', '.js', '.ts', '.go', '.rs'}
        config_extensions = {'.toml', '.yaml', '.yml', '.json', '.md', '.txt'}
        
        for file_path in codebase_path.rglob('*'):
            if file_path.is_file():
                # Skip hidden files and common exclude patterns
                if any(part.startswith('.') for part in file_path.parts):
                    continue
                
                # Skip common exclude directories
                if any(part in {'node_modules', '__pycache__', '.git', 'target', 'build', 'dist'} 
                       for part in file_path.parts):
                    continue
                
                # Include code and config files
                if file_path.suffix in code_extensions or file_path.suffix in config_extensions:
                    relevant_files.append(file_path)
        
        return relevant_files
    
    def _build_codebase_content(self, files: List[Path], model_config: ModelContextConfig) -> str:
        """Build codebase content within context window limits."""
        content_parts = []
        current_tokens = 0
        max_tokens = model_config.recommended_max_input or model_config.input_tokens
        
        for file_path in files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    file_content = f.read()
                
                # Estimate tokens for this file
                file_tokens = estimate_token_count(file_content)
                
                # Check if adding this file would exceed limits
                if current_tokens + file_tokens > max_tokens:
                    # Try to add just the file header
                    header_content = f"# {file_path.name}\n```\n{file_content[:1000]}...\n```\n"
                    header_tokens = estimate_token_count(header_content)
                    
                    if current_tokens + header_tokens <= max_tokens:
                        content_parts.append(header_content)
                        current_tokens += header_tokens
                    break
                
                # Add full file content
                file_header = f"# {file_path}\n```\n{file_content}\n```\n"
                content_parts.append(file_header)
                current_tokens += file_tokens
                
            except Exception as e:
                # Skip files that can't be read
                continue
        
        return "\n".join(content_parts)
    
    def get_usage_stats(self) -> Dict[str, int]:
        """Get usage statistics for different models."""
        return self._usage_stats.copy()
    
    def get_context_analysis(self, text: str) -> Dict[str, any]:
        """Analyze text and provide context window recommendations."""
        estimated_tokens = estimate_token_count(text)
        
        analysis = {
            "estimated_tokens": estimated_tokens,
            "suitable_models": [],
            "recommended_model": None,
            "context_utilization": {}
        }
        
        # Find suitable models
        for model_name, config in get_models_with_large_context().items():
            if can_fit_in_context(model_name, text):
                utilization = (estimated_tokens / config.input_tokens) * 100
                analysis["suitable_models"].append({
                    "model": model_name,
                    "input_tokens": config.input_tokens,
                    "utilization_percent": utilization,
                    "description": config.description
                })
                analysis["context_utilization"][model_name] = utilization
        
        # Sort by utilization (prefer models that use context efficiently)
        analysis["suitable_models"].sort(key=lambda x: x["utilization_percent"])
        
        if analysis["suitable_models"]:
            analysis["recommended_model"] = analysis["suitable_models"][0]["model"]
        
        return analysis
