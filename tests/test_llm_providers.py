"""Test LLM provider functionality."""

import pytest
from vericoding.core.llm_providers import (
    LLMProvider,
    AnthropicProvider,
    OpenAIProvider,
    DeepSeekProvider,
)


class TestLLMProviders:
    """Test LLM provider classes and inheritance."""

    def test_provider_imports(self):
        """Test that LLM provider classes can be imported."""
        # All these should be importable without errors
        assert LLMProvider is not None
        assert AnthropicProvider is not None
        assert OpenAIProvider is not None
        assert DeepSeekProvider is not None

    def test_provider_interface(self):
        """Test that the LLM provider interface is correct."""
        assert hasattr(LLMProvider, "call_api"), (
            "LLMProvider should have call_api method"
        )

    def test_provider_inheritance(self):
        """Test that concrete providers inherit properly from base class."""
        assert issubclass(AnthropicProvider, LLMProvider), (
            "AnthropicProvider should inherit from LLMProvider"
        )
        assert issubclass(OpenAIProvider, LLMProvider), (
            "OpenAIProvider should inherit from LLMProvider"
        )
        assert issubclass(DeepSeekProvider, LLMProvider), (
            "DeepSeekProvider should inherit from LLMProvider"
        )

    def test_abstract_base_class(self):
        """Test that LLMProvider is properly abstract."""
        # Should not be able to instantiate abstract base class directly
        with pytest.raises(TypeError):
            LLMProvider()
