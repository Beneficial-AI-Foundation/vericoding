# OpenRouter Model Guide

OpenRouter provides access to 100+ models from different providers with a single API key. Here are the most popular models you can use:

## 🔥 Recommended Models

### **Claude Models (Anthropic)**
```bash
# Claude 3.5 Sonnet - Best reasoning and coding
--llm-model anthropic/claude-3.5-sonnet

# Claude 3.5 Haiku - Fast and efficient
--llm-model anthropic/claude-3.5-haiku
```

### **GPT Models (OpenAI)**
```bash
# GPT-4o - Latest multimodal model
--llm-model openai/gpt-4o

# GPT-4o Mini - Cost-effective alternative
--llm-model openai/gpt-4o-mini

# O1 Preview - Advanced reasoning
--llm-model openai/o1-preview

# O1 Mini - Faster reasoning model
--llm-model openai/o1-mini
```

### **Gemini Models (Google)**
```bash
# Gemini Pro 1.5 - Long context, multimodal
--llm-model google/gemini-pro-1.5

# Gemini Flash 1.5 - Fast and efficient
--llm-model google/gemini-flash-1.5
```

### **Llama Models (Meta)**
```bash
# Llama 3.1 405B - Largest open model
--llm-model meta-llama/llama-3.1-405b-instruct

# Llama 3.1 70B - Good balance of performance/cost
--llm-model meta-llama/llama-3.1-70b-instruct

# Llama 3.1 8B - Fast and lightweight
--llm-model meta-llama/llama-3.1-8b-instruct
```

### **Other Notable Models**
```bash
# Mistral Large - European alternative
--llm-model mistralai/mistral-large

# DeepSeek V3 - Coding specialist
--llm-model deepseek/deepseek-chat

# Qwen 2.5 Coder - Specialized for programming
--llm-model qwen/qwen-2.5-coder-32b-instruct
```

## 🚀 Usage Examples

```bash
# Default (uses openai/gpt-4o)
python spec_to_code.py dafny ./specs

# Use Claude for best reasoning
python spec_to_code.py dafny ./specs --llm-model anthropic/claude-3.5-sonnet

# Use Gemini for long context
python spec_to_code.py dafny ./specs --llm-model google/gemini-pro-1.5

# Use Llama for cost efficiency
python spec_to_code.py dafny ./specs --llm-model meta-llama/llama-3.1-70b-instruct

# Use O1 for complex reasoning
python spec_to_code.py dafny ./specs --llm-model openai/o1-preview
```

## 💡 Model Selection Tips

- **For complex proofs**: `openai/o1-preview` or `anthropic/claude-3.5-sonnet`
- **For fast iteration**: `openai/gpt-4o-mini` or `anthropic/claude-3.5-haiku`
- **For cost optimization**: `meta-llama/llama-3.1-70b-instruct`
- **For long specifications**: `google/gemini-pro-1.5`
- **For coding tasks**: `qwen/qwen-2.5-coder-32b-instruct`

## 🔑 Setup

1. Get your OpenRouter API key from [openrouter.ai](https://openrouter.ai)
2. Add to your `.env` file:
   ```
   OPENROUTER_API_KEY=your-api-key-here
   ```
3. Start using any model with one key!

## 📊 Cost Comparison

OpenRouter shows real-time pricing and usage statistics. Check [openrouter.ai/models](https://openrouter.ai/models) for current pricing.

**Generally**:
- Most expensive: `openai/o1-preview`, `anthropic/claude-3.5-sonnet`
- Balanced: `openai/gpt-4o`, `google/gemini-pro-1.5`
- Cost-effective: `meta-llama/llama-3.1-70b-instruct`, `openai/gpt-4o-mini`
- Cheapest: `meta-llama/llama-3.1-8b-instruct`
