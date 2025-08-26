"""LLM provider abstractions and implementations."""

import os
from abc import ABC, abstractmethod
from time import time, sleep
from .config import ProcessingConfig

import anthropic


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
    def call_api(self, prompt: str) -> str:
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

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.messages.create(
                model=self.model,
                max_tokens=self.max_tokens,
                messages=[{"role": "user", "content": prompt}],
                timeout=self.timeout,
            )

            if response.content and len(response.content) > 0:
                text_content = response.content[0]
                if hasattr(text_content, "text"):
                    return text_content.text
                else:
                    return str(text_content)
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
        try:
            import openai

            self.client = openai.OpenAI(api_key=api_key)
        except ImportError:
            raise ImportError(
                "OpenAI package not installed. Install with: pip install openai"
            )

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                return response.choices[0].message.content
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
        try:
            import openai  # DeepSeek uses OpenAI-compatible API

            self.client = openai.OpenAI(
                api_key=api_key, base_url="https://api.deepseek.com"
            )
        except ImportError:
            raise ImportError(
                "OpenAI package not installed. Install with: pip install openai"
            )

    def call_api(self, prompt: str) -> str:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.max_tokens,
                timeout=self.timeout,
            )

            if response.choices and len(response.choices) > 0:
                return response.choices[0].message.content
            else:
                raise ValueError("Unexpected response format from DeepSeek API")

        except Exception as e:
            raise ValueError(f"Error calling DeepSeek API: {str(e)}")

    def get_required_env_var(self) -> str:
        return "DEEPSEEK_API_KEY"


def create_llm_provider(provider_name: str, model: str = None) -> LLMProvider:
    """Factory function to create LLM providers."""
    import sys
    
    provider_configs = {
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
        "deepseek": {
            "class": DeepSeekProvider,
            "default_model": "deepseek-chat",
            "env_var": "DEEPSEEK_API_KEY",
        },
    }

    if provider_name not in provider_configs:
        available = ", ".join(provider_configs.keys())
        print(f"Error: Unsupported LLM provider: {provider_name}. Available: {available}")
        sys.exit(1)

    config = provider_configs[provider_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var)

    if not api_key:
        print(
            f"Error: {env_var} environment variable is required for {provider_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key\n"
            f"\nNote: .env files are automatically loaded if they exist in the current or parent directory."
        )
        sys.exit(1)

    selected_model = model or config["default_model"]
    provider = config["class"](api_key, selected_model)
    print(f"✓ {provider_name.upper()} API key found and provider initialized")
    return provider





def call_llm(provider: LLMProvider, config: ProcessingConfig, prompt: str, wandb=None) -> str:
    """Call LLM with rate limiting and optional wandb logging."""
    # Rate limit
    sleep(config.api_rate_limit_delay)
    start = time()
    response = provider.call_api(prompt)
    latency_ms = (time() - start) * 1000
    if wandb and hasattr(wandb, "log"):
        wandb.log({
            "llm/calls": 1,
            "llm/latency_ms": latency_ms,
            "llm/model": config.llm_model or config.llm_provider
        })
    return response
