"""Test LLM provider functionality."""

import os
from unittest.mock import Mock, patch
import pytest
from vericoding.core.llm_providers import (
    LLMProvider,
    AnthropicProvider,
    OpenAIProvider,
    DeepSeekProvider,
    create_llm_provider,
)


class TestLLMProviderAbstract:
    """Test abstract LLM provider base class."""

    def test_abstract_base_class_cannot_be_instantiated(self):
        """Test that LLMProvider cannot be instantiated directly."""
        with pytest.raises(TypeError, match="Can't instantiate abstract class"):
            LLMProvider(api_key="test", model="test")

    def test_abstract_methods_defined(self):
        """Test that required abstract methods are defined."""
        assert hasattr(LLMProvider, "call_api")
        assert hasattr(LLMProvider, "get_required_env_var")

        # Check they are abstract
        assert getattr(LLMProvider.call_api, "__isabstractmethod__", False)
        assert getattr(LLMProvider.get_required_env_var, "__isabstractmethod__", False)


class TestAnthropicProvider:
    """Test Anthropic Claude provider implementation."""

    def test_initialization_with_defaults(self):
        """Test provider initializes with default model."""
        provider = AnthropicProvider(api_key="test-key")
        assert provider.api_key == "test-key"
        assert provider.model == "claude-sonnet-4-20250514"
        assert provider.max_tokens == 16384
        assert provider.timeout == 60.0

    def test_initialization_with_custom_params(self):
        """Test provider initializes with custom parameters."""
        provider = AnthropicProvider(
            api_key="test-key",
            model="claude-3-opus-20240229",
            max_tokens=4096,
            timeout=120.0,
        )
        assert provider.model == "claude-3-opus-20240229"
        assert provider.max_tokens == 4096
        assert provider.timeout == 120.0

    def test_get_required_env_var(self):
        """Test required environment variable name."""
        provider = AnthropicProvider(api_key="test")
        assert provider.get_required_env_var() == "ANTHROPIC_API_KEY"

    @patch("anthropic.Anthropic")
    def test_call_api_success(self, mock_anthropic):
        """Test successful API call."""
        # Setup mock response
        mock_response = Mock()
        mock_text_content = Mock()
        mock_text_content.text = "Test response from Claude"
        mock_response.content = [mock_text_content]
        
        # Mock usage
        mock_usage = Mock()
        mock_usage.input_tokens = 10
        mock_usage.output_tokens = 20
        mock_response.usage = mock_usage

        mock_client = Mock()
        mock_client.messages.create.return_value = mock_response
        mock_anthropic.return_value = mock_client

        # Test API call
        provider = AnthropicProvider(api_key="test-key")
        result = provider.call_api("Test prompt")

        assert result.text == "Test response from Claude"
        assert result.input_tokens == 10
        assert result.output_tokens == 20
        mock_client.messages.create.assert_called_once_with(
            model="claude-sonnet-4-20250514",
            max_tokens=16384,
            messages=[{"role": "user", "content": "Test prompt"}],
            timeout=60.0,
        )

    @patch("anthropic.Anthropic")
    def test_call_api_empty_response(self, mock_anthropic):
        """Test API call with empty response."""
        mock_response = Mock()
        mock_response.content = []

        mock_client = Mock()
        mock_client.messages.create.return_value = mock_response
        mock_anthropic.return_value = mock_client

        provider = AnthropicProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Unexpected response format"):
            provider.call_api("Test prompt")

    @patch("anthropic.Anthropic")
    def test_call_api_anthropic_error(self, mock_anthropic):
        """Test API call with Anthropic API error."""
        import anthropic

        mock_client = Mock()

        # Create a proper exception that inherits from BaseException
        class MockAPIError(anthropic.APIError, Exception):
            def __init__(self, message):
                Exception.__init__(self, message)
                self.message = message

        mock_client.messages.create.side_effect = MockAPIError("API Error")
        mock_anthropic.return_value = mock_client

        provider = AnthropicProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Anthropic API error"):
            provider.call_api("Test prompt")

    @patch("anthropic.Anthropic")
    def test_call_api_generic_error(self, mock_anthropic):
        """Test API call with generic error."""
        mock_client = Mock()
        mock_client.messages.create.side_effect = Exception("Network error")
        mock_anthropic.return_value = mock_client

        provider = AnthropicProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Error calling Claude API"):
            provider.call_api("Test prompt")

    @patch("anthropic.Anthropic")
    def test_call_api_response_without_text_attribute(self, mock_anthropic):
        """Test API call with response content that doesn't have text attribute."""
        mock_response = Mock()
        # Create a mock object that doesn't have text attribute but can be stringified
        mock_text_content = Mock(spec=[])
        # Override the __str__ method by setting the return value directly
        type(mock_text_content).__str__ = Mock(return_value="String representation")
        mock_response.content = [mock_text_content]
        
        # Mock usage
        mock_usage = Mock()
        mock_usage.input_tokens = 5
        mock_usage.output_tokens = 15
        mock_response.usage = mock_usage

        mock_client = Mock()
        mock_client.messages.create.return_value = mock_response
        mock_anthropic.return_value = mock_client

        provider = AnthropicProvider(api_key="test-key")
        result = provider.call_api("Test prompt")

        assert result.text == "String representation"
        assert result.input_tokens == 5
        assert result.output_tokens == 15


class TestOpenAIProvider:
    """Test OpenAI GPT provider implementation."""

    @patch("openai.OpenAI")
    def test_initialization_with_defaults(self, mock_openai_class):
        """Test provider initializes with default model."""
        mock_client = Mock()
        mock_openai_class.return_value = mock_client

        provider = OpenAIProvider(api_key="test-key")
        assert provider.api_key == "test-key"
        assert provider.model == "gpt-4o"


    @patch("openai.OpenAI")
    def test_get_required_env_var(self, mock_openai_class):
        """Test required environment variable name."""
        mock_client = Mock()
        mock_openai_class.return_value = mock_client

        provider = OpenAIProvider(api_key="test")
        assert provider.get_required_env_var() == "OPENAI_API_KEY"

    @patch("openai.OpenAI")
    def test_call_api_success(self, mock_openai_class):
        """Test successful API call."""
        # Setup mock response
        mock_choice = Mock()
        mock_choice.message.content = "Test response from GPT"
        mock_response = Mock()
        mock_response.choices = [mock_choice]
        
        # Mock usage
        mock_usage = Mock()
        mock_usage.prompt_tokens = 8
        mock_usage.completion_tokens = 12
        mock_response.usage = mock_usage

        # Mock client
        mock_client = Mock()
        mock_client.chat.completions.create.return_value = mock_response
        mock_openai_class.return_value = mock_client

        provider = OpenAIProvider(api_key="test-key")
        result = provider.call_api("Test prompt")

        assert result.text == "Test response from GPT"
        assert result.input_tokens == 8
        assert result.output_tokens == 12
        mock_client.chat.completions.create.assert_called_once_with(
            model="gpt-4o",
            messages=[{"role": "user", "content": "Test prompt"}],
            max_tokens=16384,
            timeout=60.0,
        )

    @patch("openai.OpenAI")
    def test_call_api_empty_choices(self, mock_openai_class):
        """Test API call with empty choices."""
        mock_response = Mock()
        mock_response.choices = []

        # Mock client
        mock_client = Mock()
        mock_client.chat.completions.create.return_value = mock_response
        mock_openai_class.return_value = mock_client

        provider = OpenAIProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Unexpected response format"):
            provider.call_api("Test prompt")

    @patch("builtins.__import__")
    def test_call_api_error(self, mock_import):
        """Test API call with error."""
        # Mock openai module
        mock_openai = Mock()
        mock_client = Mock()
        mock_client.chat.completions.create.side_effect = Exception("API error")
        mock_openai.OpenAI.return_value = mock_client
        mock_import.return_value = mock_openai

        provider = OpenAIProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Error calling OpenAI API"):
            provider.call_api("Test prompt")


class TestDeepSeekProvider:
    """Test DeepSeek provider implementation."""

    @patch("openai.OpenAI")
    def test_initialization_with_custom_base_url(self, mock_openai_class):
        """Test provider initializes with DeepSeek base URL."""
        mock_client = Mock()
        mock_openai_class.return_value = mock_client

        DeepSeekProvider(api_key="test-key")
        mock_openai_class.assert_called_once_with(
            api_key="test-key", base_url="https://api.deepseek.com"
        )


    @patch("openai.OpenAI")
    def test_get_required_env_var(self, mock_openai_class):
        """Test required environment variable name."""
        mock_client = Mock()
        mock_openai_class.return_value = mock_client

        provider = DeepSeekProvider(api_key="test")
        assert provider.get_required_env_var() == "DEEPSEEK_API_KEY"

    @patch("openai.OpenAI")
    def test_call_api_success(self, mock_openai_class):
        """Test successful API call."""
        # Setup mock response
        mock_choice = Mock()
        mock_choice.message.content = "Test response from DeepSeek"
        mock_response = Mock()
        mock_response.choices = [mock_choice]
        
        # Mock usage
        mock_usage = Mock()
        mock_usage.prompt_tokens = 6
        mock_usage.completion_tokens = 14
        mock_response.usage = mock_usage

        # Mock client
        mock_client = Mock()
        mock_client.chat.completions.create.return_value = mock_response
        mock_openai_class.return_value = mock_client

        provider = DeepSeekProvider(api_key="test-key")
        result = provider.call_api("Test prompt")

        assert result.text == "Test response from DeepSeek"
        assert result.input_tokens == 6
        assert result.output_tokens == 14
        mock_client.chat.completions.create.assert_called_once_with(
            model="deepseek-chat",
            messages=[{"role": "user", "content": "Test prompt"}],
            max_tokens=16384,
            timeout=60.0,
        )

    @patch("openai.OpenAI")
    def test_call_api_empty_choices(self, mock_openai_class):
        """Test API call with empty choices."""
        mock_response = Mock()
        mock_response.choices = []

        # Mock client
        mock_client = Mock()
        mock_client.chat.completions.create.return_value = mock_response
        mock_openai_class.return_value = mock_client

        provider = DeepSeekProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Unexpected response format"):
            provider.call_api("Test prompt")

    @patch("builtins.__import__")
    def test_call_api_error(self, mock_import):
        """Test API call with error."""
        # Mock openai module
        mock_openai = Mock()
        mock_client = Mock()
        mock_client.chat.completions.create.side_effect = Exception("API error")
        mock_openai.OpenAI.return_value = mock_client
        mock_import.return_value = mock_openai

        provider = DeepSeekProvider(api_key="test-key")

        with pytest.raises(ValueError, match="Error calling DeepSeek API"):
            provider.call_api("Test prompt")


class TestFactoryFunction:
    """Test the create_llm_provider factory function."""

    @patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-anthropic-key"})
    def test_create_claude_provider(self):
        """Test creating Claude provider via factory."""
        provider, model = create_llm_provider("claude")
        assert isinstance(provider, AnthropicProvider)
        assert provider.api_key == "test-anthropic-key"
        assert model == "claude-sonnet-4-20250514"

    @patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test-key"})
    def test_create_claude_provider_custom_model(self):
        """Test creating Claude provider via factory."""
        provider, model = create_llm_provider("claude")
        assert isinstance(provider, AnthropicProvider)
        assert model == "claude-sonnet-4-20250514"

    @patch.dict(os.environ, {"OPENAI_API_KEY": "test-openai-key"})
    @patch("builtins.__import__")
    def test_create_openai_provider(self, mock_import):
        """Test creating OpenAI provider via factory."""
        # Mock openai module
        mock_openai = Mock()
        mock_client = Mock()
        mock_openai.OpenAI.return_value = mock_client
        mock_import.return_value = mock_openai

        provider, model = create_llm_provider("openai")
        assert isinstance(provider, OpenAIProvider)
        assert provider.api_key == "test-openai-key"
        assert model == "gpt-4o"

    @patch.dict(os.environ, {"OPENROUTER_API_KEY": "test-openrouter-key"})
    @patch("builtins.__import__")
    def test_create_deepseek_provider(self, mock_import):
        """Test creating DeepSeek provider via factory."""
        # Mock openai module
        mock_openai = Mock()
        mock_client = Mock()
        mock_openai.OpenAI.return_value = mock_client
        mock_import.return_value = mock_openai

        provider, model = create_llm_provider("deepseek")
        # deepseek uses OpenRouterProvider, not DeepSeekProvider
        assert hasattr(provider, 'api_key')
        assert model == "deepseek/deepseek-chat-v3.1"

    def test_unsupported_provider(self):
        """Test error for unsupported provider."""
        with pytest.raises(SystemExit):
            create_llm_provider("unsupported")

    def test_missing_api_key(self):
        """Test error when API key environment variable is missing."""
        with patch.dict(os.environ, {}, clear=True):
            with pytest.raises(SystemExit):
                create_llm_provider("claude")

    @patch.dict(os.environ, {"ANTHROPIC_API_KEY": ""})
    def test_empty_api_key(self):
        """Test error when API key environment variable is empty."""
        with pytest.raises(SystemExit):
            create_llm_provider("claude")

    def test_factory_error_message_format(self):
        """Test that error messages provide helpful guidance."""
        with patch.dict(os.environ, {}, clear=True):
            with pytest.raises(SystemExit):
                create_llm_provider("claude")


class TestProviderInheritance:
    """Test that concrete providers properly inherit from base class."""

    def test_all_providers_inherit_from_base(self):
        """Test inheritance relationships."""
        assert issubclass(AnthropicProvider, LLMProvider)
        assert issubclass(OpenAIProvider, LLMProvider)
        assert issubclass(DeepSeekProvider, LLMProvider)

    def test_providers_implement_required_methods(self):
        """Test that all providers implement required abstract methods."""
        providers = [AnthropicProvider, OpenAIProvider, DeepSeekProvider]

        for provider_class in providers:
            # Check that abstract methods are implemented
            assert hasattr(provider_class, "call_api")
            assert hasattr(provider_class, "get_required_env_var")

            # Ensure they're not still abstract
            assert not getattr(provider_class.call_api, "__isabstractmethod__", False)
            assert not getattr(
                provider_class.get_required_env_var, "__isabstractmethod__", False
            )

    def test_base_class_initialization_parameters(self):
        """Test that base class accepts expected initialization parameters."""
        # This tests by checking what parameters concrete classes pass to super()
        with patch("anthropic.Anthropic"):
            provider = AnthropicProvider(
                api_key="test", model="test-model", max_tokens=1000, timeout=30.0
            )
            assert provider.api_key == "test"
            assert provider.model == "test-model"
            assert provider.max_tokens == 1000
            assert provider.timeout == 30.0


class TestProviderIntegration:
    """Integration tests for provider functionality."""

    @pytest.mark.integration
    def test_factory_creates_working_instances(self):
        """Test that factory creates properly configured instances."""
        test_cases = [
            ("claude", "ANTHROPIC_API_KEY", AnthropicProvider),
        ]

        for provider_name, env_var, expected_class in test_cases:
            with patch.dict(os.environ, {env_var: "test-key"}):
                with patch("anthropic.Anthropic"):  # Only needed for Anthropic
                    provider, model = create_llm_provider(provider_name)
                    assert isinstance(provider, expected_class)
                    assert provider.api_key == "test-key"
                    assert hasattr(provider, "call_api")
                    assert callable(provider.call_api)

    @pytest.mark.unit
    def test_error_handling_consistency(self):
        """Test that all providers handle errors consistently."""
        # Test Anthropic provider
        with patch("anthropic.Anthropic") as mock_anthropic:
            mock_client = Mock()
            mock_client.messages.create.side_effect = Exception("Test error")
            mock_anthropic.return_value = mock_client

            provider = AnthropicProvider(api_key="test")
            with pytest.raises(ValueError):
                provider.call_api("test prompt")

        # Test OpenAI and DeepSeek providers (they use the same openai client)
        openai_providers = [OpenAIProvider, DeepSeekProvider]
        for provider_class in openai_providers:
            with patch("builtins.__import__") as mock_import:
                # Mock openai module
                mock_openai = Mock()
                mock_client = Mock()
                mock_client.chat.completions.create.side_effect = Exception(
                    "Test error"
                )
                mock_openai.OpenAI.return_value = mock_client
                mock_import.return_value = mock_openai

                provider = provider_class(api_key="test")
                with pytest.raises(ValueError):
                    provider.call_api("test prompt")
