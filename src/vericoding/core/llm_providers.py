"""LLM provider abstractions and implementations."""

import os
from abc import ABC, abstractmethod

import anthropic
from typing import Optional


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

    def __init__(self, api_key: str, model: str = "gpt-4o", reasoning_effort: str | None = None, **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.reasoning_effort = reasoning_effort
        try:
            import openai

            self.client = openai.OpenAI(api_key=api_key)
        except ImportError:
            raise ImportError(
                "OpenAI package not installed. Install with: pip install openai"
            )

    def call_api(self, prompt: str) -> str:
        def _should_use_responses(model: str) -> bool:
            m = model.lower() if model else ""
            return any(tok in m for tok in ["gpt-5", "o4", "reason", "gpt-4o-reasoning"])

        try:
            if _should_use_responses(self.model):
                # Use Responses API for reasoning models
                try:
                    kwargs: dict = {"model": self.model, "input": prompt}
                    # Newer SDK uses max_output_tokens instead of max_tokens
                    kwargs["max_output_tokens"] = self.max_tokens
                    if self.reasoning_effort:
                        kwargs["reasoning"] = {"effort": self.reasoning_effort}
                    resp = self.client.responses.create(**kwargs)
                    # Prefer output_text when available
                    if hasattr(resp, "output_text") and getattr(resp, "output_text"):
                        return getattr(resp, "output_text")
                    # Next: try concatenating text from items in `output`
                    out = []
                    if hasattr(resp, "output") and getattr(resp, "output"):
                        for item in getattr(resp, "output"):
                            # Try item.text first
                            if hasattr(item, "text") and item.text:
                                out.append(item.text)
                            # Try item.content (list of segments)
                            segs = getattr(item, "content", None)
                            if isinstance(segs, (list, tuple)):
                                for seg in segs:
                                    t = getattr(seg, "text", None)
                                    if t:
                                        out.append(t)
                    if out:
                        return "\n".join(out)
                    # Could not extract text, fall back to Chat Completions
                    raise ValueError("No text in Responses API output")
                except Exception:
                    # Fallback to Chat Completions
                    pass

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


class MockProvider(LLMProvider):
    """Mock provider for offline/testing. Returns the code embedded in the prompt.

    Heuristics:
    - If the prompt contains a marker like "Code Below:" or
      "LEAN SPECIFICATION WITH EMPTY DEFINITIONS AND PROOF BODIES:",
      return everything after the last such marker.
    - Otherwise, return the prompt verbatim (the extractor will try to pull code).
    """

    def __init__(self, api_key: str = "", model: str = "mock", **kwargs):
        super().__init__(api_key, model, **kwargs)

    def call_api(self, prompt: str) -> str:
        split_markers = [
            "Code Below:",
            "LEAN SPECIFICATION WITH EMPTY DEFINITIONS AND PROOF BODIES:",
        ]
        last_idx: Optional[int] = None
        for marker in split_markers:
            idx = prompt.rfind(marker)
            if idx != -1:
                last_idx = max(last_idx or -1, idx)
        if last_idx is not None and last_idx >= 0:
            # Return the content after the marker
            after = prompt[last_idx:]
            return after.split("\n", 1)[1] if "\n" in after else ""
        return prompt

    def get_required_env_var(self) -> str:
        return ""  # No env var required


def create_llm_provider(provider_name: str, model: str = None, **kwargs) -> LLMProvider:
    """Factory function to create LLM providers."""
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
        "mock": {
            "class": MockProvider,
            "default_model": "mock",
            "env_var": "",  # No key required
        },
    }

    if provider_name not in provider_configs:
        available = ", ".join(provider_configs.keys())
        raise ValueError(
            f"Unsupported LLM provider: {provider_name}. Available: {available}"
        )

    config = provider_configs[provider_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var) if env_var else ""

    if env_var and not api_key:
        raise ValueError(
            f"{env_var} environment variable is required for {provider_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key"
        )

    selected_model = model or config["default_model"]
    return config["class"](api_key, selected_model, **kwargs)
