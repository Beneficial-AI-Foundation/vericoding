"""Context window configuration for different LLM models."""

from dataclasses import dataclass
from typing import Dict, Optional


@dataclass
class ModelContextConfig:
    """Configuration for a model's context window capabilities."""
    
    model_name: str
    input_tokens: int
    output_tokens: int
    total_tokens: int
    description: str
    recommended_max_input: Optional[int] = None
    recommended_max_output: Optional[int] = None


# Context window configurations for different models
MODEL_CONTEXT_CONFIGS: Dict[str, ModelContextConfig] = {
    # Claude models
    "claude-3-5-sonnet-20241022": ModelContextConfig(
        model_name="claude-3-5-sonnet-20241022",
        input_tokens=1_000_000,  # 1M input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=1_200_000,  # 1.2M total tokens
        description="Claude 3.5 Sonnet with 1M input context window",
        recommended_max_input=800_000,  # Leave some buffer
        recommended_max_output=150_000,  # Leave some buffer
    ),
    "claude-3-5-haiku-20241022": ModelContextConfig(
        model_name="claude-3-5-haiku-20241022",
        input_tokens=200_000,    # 200K input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=400_000,    # 400K total tokens
        description="Claude 3.5 Haiku with 200K input context window",
        recommended_max_input=150_000,
        recommended_max_output=150_000,
    ),
    "claude-3-opus-20240229": ModelContextConfig(
        model_name="claude-3-opus-20240229",
        input_tokens=200_000,    # 200K input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=400_000,    # 400K total tokens
        description="Claude 3 Opus with 200K input context window",
        recommended_max_input=150_000,
        recommended_max_output=150_000,
    ),
    "claude-3-sonnet-20240229": ModelContextConfig(
        model_name="claude-3-sonnet-20240229",
        input_tokens=200_000,    # 200K input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=400_000,    # 400K total tokens
        description="Claude 3 Sonnet with 200K input context window",
        recommended_max_input=150_000,
        recommended_max_output=150_000,
    ),
    "claude-3-haiku-20240307": ModelContextConfig(
        model_name="claude-3-haiku-20240307",
        input_tokens=200_000,    # 200K input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=400_000,    # 400K total tokens
        description="Claude 3 Haiku with 200K input context window",
        recommended_max_input=150_000,
        recommended_max_output=150_000,
    ),
    # Legacy models (for backward compatibility)
    "claude-sonnet-4-20250514": ModelContextConfig(
        model_name="claude-sonnet-4-20250514",
        input_tokens=200_000,    # 200K input tokens
        output_tokens=200_000,   # 200K output tokens
        total_tokens=400_000,    # 400K total tokens
        description="Claude Sonnet 4 with 200K input context window",
        recommended_max_input=150_000,
        recommended_max_output=150_000,
    ),
    
    # OpenAI models
    "gpt-4o": ModelContextConfig(
        model_name="gpt-4o",
        input_tokens=128_000,    # 128K input tokens
        output_tokens=128_000,   # 128K output tokens
        total_tokens=256_000,    # 256K total tokens
        description="GPT-4o with 128K input context window",
        recommended_max_input=100_000,
        recommended_max_output=100_000,
    ),
    "gpt-4o-mini": ModelContextConfig(
        model_name="gpt-4o-mini",
        input_tokens=128_000,    # 128K input tokens
        output_tokens=128_000,   # 128K output tokens
        total_tokens=256_000,    # 256K total tokens
        description="GPT-4o Mini with 128K input context window",
        recommended_max_input=100_000,
        recommended_max_output=100_000,
    ),
    
    # DeepSeek models
    "deepseek-chat": ModelContextConfig(
        model_name="deepseek-chat",
        input_tokens=128_000,    # 128K input tokens
        output_tokens=128_000,   # 128K output tokens
        total_tokens=256_000,    # 256K total tokens
        description="DeepSeek Chat with 128K input context window",
        recommended_max_input=100_000,
        recommended_max_output=100_000,
    ),
}


def get_model_context_config(model_name: str) -> Optional[ModelContextConfig]:
    """Get context configuration for a specific model."""
    return MODEL_CONTEXT_CONFIGS.get(model_name)


def get_available_models() -> Dict[str, ModelContextConfig]:
    """Get all available model configurations."""
    return MODEL_CONTEXT_CONFIGS.copy()


def get_models_by_provider(provider: str) -> Dict[str, ModelContextConfig]:
    """Get models filtered by provider."""
    provider_models = {}
    
    if provider.lower() == "claude" or provider.lower() == "anthropic":
        for model_name, config in MODEL_CONTEXT_CONFIGS.items():
            if model_name.startswith("claude"):
                provider_models[model_name] = config
    elif provider.lower() == "openai":
        for model_name, config in MODEL_CONTEXT_CONFIGS.items():
            if model_name.startswith("gpt"):
                provider_models[model_name] = config
    elif provider.lower() == "deepseek":
        for model_name, config in MODEL_CONTEXT_CONFIGS.items():
            if model_name.startswith("deepseek"):
                provider_models[model_name] = config
    
    return provider_models


def get_models_with_large_context(min_input_tokens: int = 500_000) -> Dict[str, ModelContextConfig]:
    """Get models with large context windows (useful for processing large codebases)."""
    large_context_models = {}
    
    for model_name, config in MODEL_CONTEXT_CONFIGS.items():
        if config.input_tokens >= min_input_tokens:
            large_context_models[model_name] = config
    
    return large_context_models


def estimate_token_count(text: str) -> int:
    """Rough estimation of token count for text (approximate)."""
    # This is a very rough estimation - in practice, you'd want to use a proper tokenizer
    # For English text, roughly 1 token ≈ 4 characters
    return len(text) // 4


def can_fit_in_context(model_name: str, input_text: str, output_tokens: int = 8192) -> bool:
    """Check if input text and expected output can fit in model's context window."""
    config = get_model_context_config(model_name)
    if not config:
        return False
    
    estimated_input_tokens = estimate_token_count(input_text)
    total_required = estimated_input_tokens + output_tokens
    
    return total_required <= config.total_tokens


def get_optimal_model_for_text(input_text: str, output_tokens: int = 8192, 
                              preferred_provider: Optional[str] = None) -> Optional[str]:
    """Find the optimal model for processing a given text."""
    estimated_input_tokens = estimate_token_count(input_text)
    total_required = estimated_input_tokens + output_tokens
    
    # Filter by provider if specified
    if preferred_provider:
        available_models = get_models_by_provider(preferred_provider)
    else:
        available_models = MODEL_CONTEXT_CONFIGS
    
    # Find models that can handle the text
    suitable_models = []
    for model_name, config in available_models.items():
        if total_required <= config.total_tokens:
            suitable_models.append((model_name, config))
    
    if not suitable_models:
        return None
    
    # Sort by efficiency (prefer smaller context windows for smaller texts)
    suitable_models.sort(key=lambda x: x[1].total_tokens)
    
    return suitable_models[0][0]
