"""LLM provider abstractions and implementations."""

import os
import threading
from abc import ABC, abstractmethod
from time import time, sleep
from dataclasses import dataclass
from typing import Optional
# from .config import ProcessingConfig

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
        self, api_key: str, model: str, max_tokens: int = 16384, timeout: float = 60.0
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

class OpenRouterProvider(LLMProvider):
    """OpenRouter LLM provider."""

    def __init__(self, api_key: str, model: str = "openai/gpt-5", **kwargs):
        super().__init__(api_key, model, **kwargs)
        self.client = openai.OpenAI(
            api_key=api_key, base_url="https://openrouter.ai/api/v1"
        )

    def call_api(self, messages: list[dict], temperature: float = 0.3, max_tokens: int = None) -> LLMResponse:
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=messages,
                max_tokens=max_tokens if max_tokens is not None else self.max_tokens,
                timeout=self.timeout,
                temperature=temperature,
            )
            if response.choices and len(response.choices) > 0:
                text = response.choices[0].message.content
                if not text or not str(text).strip():
                    print(response)
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