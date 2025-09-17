"""LLM provider abstractions and implementations."""

import json
import os
import threading
from abc import ABC, abstractmethod
from dataclasses import dataclass
from time import sleep, time
from typing import Any, Dict, List, Optional, Tuple, TYPE_CHECKING

from .config import ProcessingConfig

import anthropic
import openai

if TYPE_CHECKING:
    from vericoding.mcp.lean import LeanMCPManager


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
    print(f"✓ Initialized provider for '{llm_name}' using {env_var} (model: {selected_model})")
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

def call_llm(
    provider: LLMProvider,
    config: ProcessingConfig,
    prompt: str,
    wandb=None,
    *,
    lean_mcp_manager: "LeanMCPManager | None" = None,
) -> str:
    """Call LLM with optional Lean MCP tool support and wandb logging."""

    sleep(config.api_rate_limit_delay)
    start = time()

    if (
        config.language == "lean"
        and getattr(config, "use_lean_mcp", False)
        and lean_mcp_manager is not None
    ):
        try:
            text, input_tokens, output_tokens, call_count = _call_llm_with_mcp(
                provider, config, prompt, lean_mcp_manager
            )
        except Exception as mcp_error:  # pylint: disable=broad-except
            print(f"⚠️  Lean MCP tool execution failed: {mcp_error}")
            response = provider.call_api(prompt)
            text = response.text
            input_tokens = response.input_tokens
            output_tokens = response.output_tokens
            call_count = 1
    else:
        response = provider.call_api(prompt)
        text = response.text
        input_tokens = response.input_tokens
        output_tokens = response.output_tokens
        call_count = 1

    latency_ms = (time() - start) * 1000

    with _token_stats_lock:
        _global_token_stats["input_tokens"] += input_tokens
        _global_token_stats["output_tokens"] += output_tokens
        _global_token_stats["total_calls"] += call_count

    if wandb and hasattr(wandb, "log") and hasattr(wandb, "run") and wandb.run:
        model_name = getattr(provider, "model", None) or config.llm
        try:
            wandb.log(
                {
                    "llm/calls": call_count,
                    "llm/latency_ms": latency_ms,
                    "llm/model": model_name,
                }
            )
        except Exception as wandb_error:  # pylint: disable=broad-except
            print(f"There was a W&B error {wandb_error} in llm_providers.py")

    return text


def _call_llm_with_mcp(
    provider: LLMProvider,
    config: ProcessingConfig,
    prompt: str,
    lean_mcp_manager: "LeanMCPManager",
) -> Tuple[str, int, int, int]:
    """Call an OpenAI-compatible model with Lean MCP tool support."""

    if not hasattr(provider, "client"):
        response = provider.call_api(prompt)
        return response.text, response.input_tokens, response.output_tokens, 1

    system_prompt = (
        lean_mcp_manager.instructions
        or "You have access to Lean LSP tooling via MCP. Use the tools when they help you understand or verify Lean code."
    )

    messages: List[Dict[str, Any]] = []
    if system_prompt:
        messages.append({"role": "system", "content": system_prompt})
    messages.append({"role": "user", "content": prompt})

    tools = lean_mcp_manager.openai_tools()
    total_input_tokens = 0
    total_output_tokens = 0
    api_calls = 0
    max_iterations = 8

    while api_calls < max_iterations:
        api_calls += 1

        request_kwargs: Dict[str, Any] = {
            "model": provider.model,
            "messages": messages,
            "max_tokens": provider.max_tokens,
            "timeout": provider.timeout,
        }
        if tools:
            request_kwargs["tools"] = tools
            request_kwargs["tool_choice"] = "auto"

        response = provider.client.chat.completions.create(**request_kwargs)

        usage = getattr(response, "usage", None)
        if usage is not None:
            total_input_tokens += getattr(usage, "prompt_tokens", 0) or 0
            total_output_tokens += getattr(usage, "completion_tokens", 0) or 0

        if not response.choices:
            break

        choice = response.choices[0]
        message = choice.message

        assistant_payload: Dict[str, Any] = {
            "role": "assistant",
            "content": message.content,
        }
        tool_calls = getattr(message, "tool_calls", None)
        if tool_calls:
            assistant_payload["tool_calls"] = tool_calls
        messages.append(assistant_payload)

        if choice.finish_reason == "tool_calls" and tool_calls:
            for tool_call in tool_calls:
                tool_name = getattr(tool_call.function, "name", "")
                raw_arguments = getattr(tool_call.function, "arguments", "") or "{}"
                try:
                    arguments = json.loads(raw_arguments)
                except json.JSONDecodeError:
                    arguments = {"raw": raw_arguments}

                try:
                    tool_output = lean_mcp_manager.call_tool(tool_name, arguments)
                except Exception as tool_error:  # pylint: disable=broad-except
                    tool_output = f"Tool `{tool_name}` raised an error: {tool_error}"

                messages.append(
                    {
                        "role": "tool",
                        "tool_call_id": getattr(tool_call, "id", ""),
                        "name": tool_name,
                        "content": tool_output or "(no output)",
                    }
                )

            continue

        final_content = message.content or ""
        return final_content, total_input_tokens, total_output_tokens, api_calls

    # If we exit the loop without a definitive content, fall back to last assistant text
    fallback_content = ""
    for msg in reversed(messages):
        if msg.get("role") == "assistant" and msg.get("content"):
            fallback_content = msg["content"]
            break

    return fallback_content, total_input_tokens, total_output_tokens, api_calls
