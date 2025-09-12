"""Tests for context window configuration."""

import pytest
from vericoding.core.context_window_config import (
    get_model_context_config,
    get_available_models,
    get_models_by_provider,
    get_models_with_large_context,
    estimate_token_count,
    can_fit_in_context,
    get_optimal_model_for_text,
    ModelContextConfig,
)


class TestModelContextConfig:
    """Test ModelContextConfig dataclass."""
    
    def test_model_context_config_creation(self):
        """Test creating a ModelContextConfig instance."""
        config = ModelContextConfig(
            model_name="test-model",
            input_tokens=1000000,
            output_tokens=200000,
            total_tokens=1200000,
            description="Test model with 1M input tokens",
            recommended_max_input=800000,
            recommended_max_output=150000,
        )
        
        assert config.model_name == "test-model"
        assert config.input_tokens == 1000000
        assert config.output_tokens == 200000
        assert config.total_tokens == 1200000
        assert config.description == "Test model with 1M input tokens"
        assert config.recommended_max_input == 800000
        assert config.recommended_max_output == 150000


class TestContextWindowFunctions:
    """Test context window utility functions."""
    
    def test_get_model_context_config_existing(self):
        """Test getting context config for existing model."""
        config = get_model_context_config("claude-3-5-sonnet-20241022")
        
        assert config is not None
        assert config.model_name == "claude-3-5-sonnet-20241022"
        assert config.input_tokens == 1000000
        assert config.output_tokens == 200000
        assert config.total_tokens == 1200000
    
    def test_get_model_context_config_nonexistent(self):
        """Test getting context config for non-existent model."""
        config = get_model_context_config("nonexistent-model")
        assert config is None
    
    def test_get_available_models(self):
        """Test getting all available models."""
        models = get_available_models()
        
        assert isinstance(models, dict)
        assert len(models) > 0
        
        # Check that we have the new 1M token model
        assert "claude-3-5-sonnet-20241022" in models
        assert models["claude-3-5-sonnet-20241022"].input_tokens == 1000000
    
    def test_get_models_by_provider_claude(self):
        """Test getting Claude models."""
        claude_models = get_models_by_provider("claude")
        
        assert isinstance(claude_models, dict)
        assert len(claude_models) > 0
        
        # All models should be Claude models
        for model_name in claude_models.keys():
            assert model_name.startswith("claude")
    
    def test_get_models_by_provider_openai(self):
        """Test getting OpenAI models."""
        openai_models = get_models_by_provider("openai")
        
        assert isinstance(openai_models, dict)
        assert len(openai_models) > 0
        
        # All models should be GPT models
        for model_name in openai_models.keys():
            assert model_name.startswith("gpt")
    
    def test_get_models_with_large_context(self):
        """Test getting models with large context windows."""
        large_context_models = get_models_with_large_context(500000)
        
        assert isinstance(large_context_models, dict)
        
        # All models should have at least 500K input tokens
        for config in large_context_models.values():
            assert config.input_tokens >= 500000
    
    def test_get_models_with_large_context_1m(self):
        """Test getting models with 1M+ input tokens."""
        one_million_models = get_models_with_large_context(1000000)
        
        # Should include the new Claude 3.5 Sonnet
        assert "claude-3-5-sonnet-20241022" in one_million_models
        assert one_million_models["claude-3-5-sonnet-20241022"].input_tokens == 1000000


class TestTokenEstimation:
    """Test token estimation functions."""
    
    def test_estimate_token_count_simple(self):
        """Test simple token estimation."""
        text = "Hello world"
        tokens = estimate_token_count(text)
        
        # Should be roughly 3 tokens (Hello + world + space)
        assert tokens > 0
        assert tokens <= 5
    
    def test_estimate_token_count_large(self):
        """Test token estimation for large text."""
        text = "Hello world " * 1000  # 3000 words
        tokens = estimate_token_count(text)
        
        # Should be roughly 3000 tokens
        assert tokens > 2000
        assert tokens < 4000
    
    def test_estimate_token_count_empty(self):
        """Test token estimation for empty text."""
        tokens = estimate_token_count("")
        assert tokens == 0
    
    def test_estimate_token_count_code(self):
        """Test token estimation for code."""
        code = """
def hello_world():
    print("Hello, world!")
    return True
"""
        tokens = estimate_token_count(code)
        assert tokens > 0


class TestContextFitting:
    """Test context fitting functions."""
    
    def test_can_fit_in_context_small_text(self):
        """Test if small text fits in context."""
        small_text = "Hello world"
        can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", small_text)
        assert can_fit is True
    
    def test_can_fit_in_context_large_text(self):
        """Test if large text fits in context."""
        # Create a very large text (more than 1M tokens)
        large_text = "Hello world " * 300000  # ~900K tokens
        can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", large_text)
        assert can_fit is True
    
    def test_can_fit_in_context_too_large(self):
        """Test if extremely large text fits in context."""
        # Create an extremely large text (more than 1.2M tokens)
        huge_text = "Hello world " * 400000  # ~1.2M tokens
        can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", huge_text)
        assert can_fit is False
    
    def test_can_fit_in_context_with_output_tokens(self):
        """Test context fitting with output tokens."""
        text = "Hello world " * 100000  # ~300K tokens
        can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", text, 100000)
        assert can_fit is True
    
    def test_can_fit_in_context_nonexistent_model(self):
        """Test context fitting with non-existent model."""
        can_fit = can_fit_in_context("nonexistent-model", "Hello world")
        assert can_fit is False


class TestOptimalModelSelection:
    """Test optimal model selection."""
    
    def test_get_optimal_model_for_small_text(self):
        """Test optimal model selection for small text."""
        small_text = "Hello world"
        optimal_model = get_optimal_model_for_text(small_text)
        
        assert optimal_model is not None
        # Should select a model with smaller context window for efficiency
    
    def test_get_optimal_model_for_large_text(self):
        """Test optimal model selection for large text."""
        large_text = "Hello world " * 200000  # ~600K tokens
        optimal_model = get_optimal_model_for_text(large_text)
        
        assert optimal_model is not None
        # Should select a model with large context window
        config = get_model_context_config(optimal_model)
        assert config.input_tokens >= 600000
    
    def test_get_optimal_model_with_preferred_provider(self):
        """Test optimal model selection with preferred provider."""
        text = "Hello world " * 100000  # ~300K tokens
        optimal_model = get_optimal_model_for_text(text, preferred_provider="claude")
        
        assert optimal_model is not None
        assert optimal_model.startswith("claude")
    
    def test_get_optimal_model_no_suitable_model(self):
        """Test optimal model selection when no model can handle the text."""
        # Create an extremely large text that no model can handle
        huge_text = "Hello world " * 1000000  # ~3M tokens
        optimal_model = get_optimal_model_for_text(huge_text)
        
        assert optimal_model is None


class TestLargeContextModels:
    """Test specific functionality for large context models."""
    
    def test_claude_3_5_sonnet_1m_context(self):
        """Test Claude 3.5 Sonnet 1M context window."""
        config = get_model_context_config("claude-3-5-sonnet-20241022")
        
        assert config is not None
        assert config.input_tokens == 1000000
        assert config.output_tokens == 200000
        assert config.total_tokens == 1200000
        assert "1M input context window" in config.description
    
    def test_large_context_model_comparison(self):
        """Test comparison of large context models."""
        large_models = get_models_with_large_context(500000)
        
        # Should have multiple models with large context
        assert len(large_models) >= 1
        
        # Claude 3.5 Sonnet should have the largest context
        claude_35_sonnet = large_models.get("claude-3-5-sonnet-20241022")
        if claude_35_sonnet:
            for model_name, config in large_models.items():
                if model_name != "claude-3-5-sonnet-20241022":
                    assert claude_35_sonnet.input_tokens >= config.input_tokens




