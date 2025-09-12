"""LLM provider abstractions and implementations."""

import os
import threading
from abc import ABC, abstractmethod
from time import time, sleep
from dataclasses import dataclass
from typing import Optional
from .config import ProcessingConfig

import anthropic
import openai


@dataclass
class LLMResponse:
    """Response from LLM API including token usage information."""
    text: str
    input_tokens: int = 0
    output_tokens: int = 0


class LLMProvider(ABC):
    """Abstract interface for LLM providers."""

    def __init__(
        self, api_key: str, model: str, max_tokens: int = 8192, timeout: float = 60.0
    ):
        self.api_key = api_key
        self.model = model
        self.max_tokens = max_tokens
        self.timeout = timeout

    @abstractmethod
    def call_api(self, prompt: str) -> LLMResponse:
        """Call the LLM API with the given prompt."""
        pass

    @abstractmethod
    def get_required_env_var(self) -> str:
        """Return the required environment variable name for API key."""
        pass


class AnthropicProvider(LLMProvider):
    """Anthropic Claude LLM provider."""

    def __init__(self, api_key: str, model: str = "claude-sonnet-4-20250514", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = anthropic.Anthropic(api_key=api_key)

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                messages=[{"role": "user", "content": prompt}],
                timeout=self.timeout,
            )

            if response.content and len(response.content) > 0:
                text_content = response.content[0]
                text = text_content.text if hasattr(text_content, "text") else str(text_content)
                if not text or not str(text).strip():
                    raise ValueError("Empty response from Anthropic API")
                
                # Extract token usage
                input_tokens = getattr(response.usage, 'input_tokens', 0) if hasattr(response, 'usage') else 0
                output_tokens = getattr(response.usage, 'output_tokens', 0) if hasattr(response, 'usage') else 0
                
                return LLMResponse(
                    text=text,
                    input_tokens=input_tokens,
                    output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from Claude API")

        except anthropic.APIError as e:
            raise ValueError(f"Anthropic API error: {str(e)}")
        except Exception as e:
            raise ValueError(f"Error calling Claude API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "ANTHROPIC_API_KEY"


class OpenAIProvider(LLMProvider):
    """OpenAI GPT LLM provider."""

    def __init__(self, api_key: str, model: str = "gpt-4o", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(api_key=api_key)

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from OpenAI API")
                
                # Extract token usage
                input_tokens = getattr(response.usage, 'prompt_tokens', 0) if hasattr(response, 'usage') else 0
                output_tokens = getattr(response.usage, 'completion_tokens', 0) if hasattr(response, 'usage') else 0
                
                return LLMResponse(
                    text=text,
                    input_tokens=input_tokens,
                    output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from OpenAI API")

        except Exception as e:
            raise ValueError(f"Error calling OpenAI API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "OPENAI_API_KEY"


class DeepSeekProvider(LLMProvider):
    """DeepSeek LLM provider."""

    def __init__(self, api_key: str, model: str = "deepseek-chat", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(
            api_key=api_key, base_url="https://api.deepseek.com"
        )

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from DeepSeek API")
                
                # Extract token usage (DeepSeek uses OpenAI-compatible format)
                input_tokens = getattr(response.usage, 'prompt_tokens', 0) if hasattr(response, 'usage') else 0
                output_tokens = getattr(response.usage, 'completion_tokens', 0) if hasattr(response, 'usage') else 0
                
                return LLMResponse(
                    text=text,
                    input_tokens=input_tokens,
                    output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from DeepSeek API")

        except Exception as e:
            raise ValueError(f"Error calling DeepSeek API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "DEEPSEEK_API_KEY"


class GrokProvider(LLMProvider):
    """Grok (xAI) LLM provider."""

    def __init__(self, api_key: str, model: str = "grok-4", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(
            api_key=api_key, base_url="https://api.x.ai/v1"
        )

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from Grok API")
                
                # Extract token usage (Grok uses OpenAI-compatible format)
                input_tokens = getattr(response.usage, 'prompt_tokens', 0) if hasattr(response, 'usage') else 0
                output_tokens = getattr(response.usage, 'completion_tokens', 0) if hasattr(response, 'usage') else 0
                
                return LLMResponse(
                    text=text,
                    input_tokens=input_tokens,
                    output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from Grok API")

        except Exception as e:
            raise ValueError(f"Error calling Grok API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "XAI_API_KEY"


class OpenRouterProvider(LLMProvider):
    """OpenRouter LLM provider."""

    def __init__(self, api_key: str, model: str = "openai/gpt-4o", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(
            api_key=api_key, base_url="https://openrouter.ai/api/v1"
        )

    def call_api(self, prompt: str) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    raise ValueError("Empty response from OpenRouter API")
                
                # Extract token usage (OpenRouter uses OpenAI-compatible format)
                input_tokens = getattr(response.usage, 'prompt_tokens', 0) if hasattr(response, 'usage') else 0
                output_tokens = getattr(response.usage, 'completion_tokens', 0) if hasattr(response, 'usage') else 0
                
                return LLMResponse(
                    text=text,
                    input_tokens=input_tokens,
                    output_tokens=output_tokens
                )
            else:
                raise ValueError("Unexpected response format from OpenRouter API")

        except Exception as e:
            raise ValueError(f"Error calling OpenRouter API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "OPENROUTER_API_KEY"


def create_llm_provider(llm_name: str) -> tuple[LLMProvider, str]:
    """Factory function to create LLM providers.
    
    Args:
        llm_name: Name of the LLM (e.g., 'claude-sonnet', 'gpt', 'claude-direct')
    
    Returns:
        tuple[LLMProvider, str]: The provider instance and the resolved model name.
    """
    import sys
    
    provider_configs = {
        "claude-sonnet": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-sonnet-4",  
            "env_var": "OPENROUTER_API_KEY",
        },
        "claude-opus": {
            "class": OpenRouterProvider,
            "default_model": "anthropic/claude-opus-4.1",  
            "env_var": "OPENROUTER_API_KEY",
        },
        "gpt": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-5",  # Latest GPT-5 (Aug 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "gpt-mini": {
            "class": OpenRouterProvider,
            "default_model": "openai/gpt-5-mini",
            "env_var": "OPENROUTER_API_KEY",
        },
        "o1": {
            "class": OpenRouterProvider,
            "default_model": "openai/o1-preview",  # O1 reasoning model
            "env_var": "OPENROUTER_API_KEY",
        },
        "gemini": {
            "class": OpenRouterProvider,
            "default_model": "google/gemini-2.5-pro",  # Latest Gemini 2.5 Pro (June 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "gemini-flash": {
            "class": OpenRouterProvider,
            "default_model": "google/gemini-2.5-flash",  # Gemini 2.5 Flash (August 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "grok": {
            "class": OpenRouterProvider,
            "default_model": "x-ai/grok-4",  # Latest Grok 4 (July 2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "grok-code": {
            "class": OpenRouterProvider,
            "default_model": "x-ai/grok-code-fast-1",
            "env_var": "OPENROUTER_API_KEY",
        },
        "deepseek": {
            "class": OpenRouterProvider,
            "default_model": "deepseek/deepseek-chat-v3.1",  # Latest DeepSeek V3
            "env_var": "OPENROUTER_API_KEY",
        },
        "glm": {
            "class": OpenRouterProvider,
            "default_model": "z-ai/glm-4.5",  # GLM-4.5 (2025)
            "env_var": "OPENROUTER_API_KEY",
        },
        "mistral-medium": {
            "class": OpenRouterProvider,
            "default_model": "mistralai/mistral-medium-3.1", 
            "env_var": "OPENROUTER_API_KEY",
        },
        "mistral-codestral": {
            "class": OpenRouterProvider,
            "default_model": "mistralai/codestral-2508", 
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwen-thinking": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwen3-30b-a3b-thinking-2507",
            "env_var": "OPENROUTER_API_KEY",
        },
        "qwen-coder": {
            "class": OpenRouterProvider,
            "default_model": "qwen/qwen3-coder-30b-a3b-instruct",
            "env_var": "OPENROUTER_API_KEY",
        },
        # Keep legacy direct providers for backwards compatibility
        "openai-direct": {
            "class": OpenAIProvider,
            "default_model": "gpt-4o",
            "env_var": "OPENAI_API_KEY",
        },
        "claude-direct": {
            "class": AnthropicProvider,
            "default_model": "claude-sonnet-4-20250514",
            "env_var": "ANTHROPIC_API_KEY",
        },
        "grok-direct": {
            "class": GrokProvider,
            "default_model": "grok-4",
            "env_var": "XAI_API_KEY",
        },
        # Legacy aliases for backwards compatibility
        "claude": {
            "class": AnthropicProvider,
            "default_model": "claude-sonnet-4-20250514",
            "env_var": "ANTHROPIC_API_KEY",
        },
        "openai": {
            "class": OpenAIProvider,
            "default_model": "gpt-4o",
            "env_var": "OPENAI_API_KEY",
        },
    }

    if llm_name not in provider_configs:
        available = ", ".join(provider_configs.keys())
        print(f"Error: Unsupported LLM: {llm_name}. Available: {available}")
        sys.exit(1)

    config = provider_configs[llm_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var)

    if not api_key:
        print(
            f"Error: {env_var} environment variable is required for {llm_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key\n"
            f"\nNote: .env files are automatically loaded if they exist in the current or parent directory."
        )
        sys.exit(1)

    selected_model = config["default_model"]
    provider = config["class"](api_key, selected_model)
    print(f"✓ {llm_name.upper()} API key found and provider initialized")
    return provider, selected_model


# Global token counter for tracking across all calls (thread-safe)
_global_token_stats = {
    "input_tokens": 0,
    "output_tokens": 0,
    "total_calls": 0
}
_token_stats_lock = threading.Lock()

def get_global_token_stats() -> dict:
    """Get the current global token usage statistics."""
    with _token_stats_lock:
        return _global_token_stats.copy()

def reset_global_token_stats():
    """Reset the global token usage statistics."""
    with _token_stats_lock:
        _global_token_stats["input_tokens"] = 0
        _global_token_stats["output_tokens"] = 0
        _global_token_stats["total_calls"] = 0

def call_llm(provider: LLMProvider, config: ProcessingConfig, prompt: str, wandb=None) -> str:
    """Call LLM with rate limiting and optional wandb logging."""
    # Rate limit
    sleep(config.api_rate_limit_delay)
    start = time()
    llm_response = provider.call_api(prompt)
    latency_ms = (time() - start) * 1000
    
    # Update global token statistics (thread-safe)
    with _token_stats_lock:
        _global_token_stats["input_tokens"] += llm_response.input_tokens
        _global_token_stats["output_tokens"] += llm_response.output_tokens
        _global_token_stats["total_calls"] += 1
    
    if wandb and hasattr(wandb, "log"):
        # Use multiple fallbacks to ensure we always have a model name
        model_name = getattr(provider, 'model', None) or config.llm
        wandb.log({
            "llm/calls": 1,
            "llm/latency_ms": latency_ms,
            "llm/model": model_name,
        })
    
    return llm_response.text
