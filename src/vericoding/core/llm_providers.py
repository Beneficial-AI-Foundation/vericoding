"""LLM provider abstractions and implementations.

Adds Claude Code SDK integration with MCP (lean-lsp-mcp) so that when the
provider is "claude" we default to using Claude Code (anthropic's agentic
runtime) rather than plain text-only Claude. This enables implicit
scaffolding and tool usage.
"""

import os
from abc import ABC, abstractmethod

import anthropic
from pathlib import Path
from typing import Any, Dict

from vericoding.utils.git_utils import get_repo_root


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


class ClaudeCodeProvider(LLMProvider):
    """Anthropic Claude Code SDK provider with MCP integration.

    This provider launches the Claude Code SDK and grants it access to
    the `lean-lsp-mcp` server via stdio, so prompts can leverage
    hover/goals/diagnostics. It also prepends CLAUDE.md as a system
    instruction layer.
    """

    def __init__(self, api_key: str, model: str = "claude-opus-4-1", **kwargs):
        super().__init__(api_key, model, **kwargs)
        try:
            from claude_code_sdk import query, ClaudeCodeOptions  # type: ignore
        except ImportError as e:
            raise ImportError(
                "claude-code-sdk is not installed. Install with: uv add claude-code-sdk"
            ) from e
        self._query = query
        self._Options = ClaudeCodeOptions

    def _load_system_prompt(self) -> str:
        # Load CLAUDE.md if present to prime the agent with repo-specific guidance
        try:
            root = get_repo_root()
            p = Path(root) / "CLAUDE.md"
            if p.exists():
                return p.read_text(encoding="utf-8")
        except Exception:
            pass
        return ""

    def call_api(self, prompt: str) -> str:
        # Build Claude Code options
        root = str(get_repo_root())
        system_md = self._load_system_prompt()
        system_prefix = (
            "You are the verifying code agent for a Lean 4 repo.\n"
            "- Use lean-lsp-mcp tools for hover, goals, diagnostics, and searches.\n"
            "- Prefer strict spec preservation; fill in `sorry` where possible.\n"
            "- Provide complete Lean code patches in response.\n"
        )
        system_prompt = (system_prefix + "\n\n" + system_md).strip()

        try:
            # Construct options with MCP server wired via lake env
            env = {"LEAN_PROJECT_PATH": root}
            mcp_servers: Dict[str, Dict[str, Any]] = {
                "lean-lsp-mcp": {
                    "type": "stdio",
                    "command": "lake",
                    "args": ["env", "uvx", "lean-lsp-mcp"],
                    "env": env,
                    "cwd": root,
                }
            }
            options = self._Options(
                model=self.model,
                cwd=root,
                allowed_tools=[
                    "Read",
                    "Write",
                    "Grep",
                    "Search",
                    "Bash",
                    "mcp__lean-lsp-mcp",
                ],
                mcp_servers=mcp_servers,
                permission_mode="accept",
            )

            # Compose messages (include system layer)
            messages = []
            if system_prompt:
                messages.append({"role": "system", "content": system_prompt})
            messages.append({"role": "user", "content": prompt})

            # Run query and accumulate assistant text output
            output_chunks: list[str] = []
            for event in self._query(messages, options):  # type: ignore
                try:
                    t = getattr(event, "type", None)
                    if t in ("assistant", "assistant_message"):
                        content = getattr(event, "content", None)
                        if isinstance(content, str):
                            output_chunks.append(content)
                        else:
                            # best-effort stringify
                            output_chunks.append(str(content))
                except Exception:
                    # Ignore non-text events (file writes, terminals, etc.)
                    continue

            text = "\n".join([c for c in output_chunks if c])
            if not text:
                text = ""  # avoid None
            return text
        except Exception as e:
            raise ValueError(f"Error running Claude Code query: {e}")

    def get_required_env_var(self) -> str:
        return "ANTHROPIC_API_KEY"


class AnthropicProvider(LLMProvider):
    """Anthropic Claude LLM provider."""

    def __init__(self, api_key: str, model: str = "claude-opus-4-1", **kwargs):
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
    provider_configs = {
        # Use Claude Code by default for Anthropic to enable MCP tooling.
        "claude": {
            "class": ClaudeCodeProvider,
            "default_model": "claude-opus-4-1",
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
        raise ValueError(
            f"Unsupported LLM provider: {provider_name}. Available: {available}"
        )

    config = provider_configs[provider_name]
    env_var = config["env_var"]
    api_key = os.getenv(env_var)

    if not api_key:
        raise ValueError(
            f"{env_var} environment variable is required for {provider_name}.\n"
            f"You can set it by:\n"
            f"1. Creating a .env file with: {env_var}=your-api-key\n"
            f"2. Setting environment variable: export {env_var}=your-api-key"
        )

    selected_model = model or config["default_model"]
    return config["class"](api_key, selected_model)
