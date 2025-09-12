#!/usr/bin/env python3
"""
Demonstration of large context window capabilities with Claude 3.5 Sonnet.

This script shows how to use the new 1M input token context window
to process large codebases and complex verification tasks.
"""

import os
import sys
from pathlib import Path

# Add the project root to the path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

from vericoding.core import (
    EnhancedLLMProvider,
    get_model_context_config,
    get_models_with_large_context,
    estimate_token_count,
    can_fit_in_context,
    get_optimal_model_for_text,
)


def demo_context_window_analysis():
    """Demonstrate context window analysis capabilities."""
    print("=== Context Window Analysis Demo ===\n")
    
    # Show available models with large context
    large_context_models = get_models_with_large_context(500_000)
    print("Models with large context windows (500K+ input tokens):")
    for model_name, config in large_context_models.items():
        print(f"  {model_name}: {config.input_tokens:,} input tokens")
        print(f"    Description: {config.description}")
        print(f"    Total tokens: {config.total_tokens:,}")
        print()
    
    # Analyze a sample text
    sample_text = "This is a sample text for analysis. " * 1000
    print(f"Sample text length: {len(sample_text)} characters")
    estimated_tokens = estimate_token_count(sample_text)
    print(f"Estimated tokens: {estimated_tokens:,}")
    
    # Check which models can handle this text
    print("\nModels that can handle this text:")
    for model_name in large_context_models.keys():
        if can_fit_in_context(model_name, sample_text):
            config = large_context_models[model_name]
            utilization = (estimated_tokens / config.input_tokens) * 100
            print(f"  {model_name}: {utilization:.1f}% context utilization")
    
    print()


def demo_optimal_model_selection():
    """Demonstrate optimal model selection."""
    print("=== Optimal Model Selection Demo ===\n")
    
    # Test with different text sizes
    test_cases = [
        ("Small text", "Hello world"),
        ("Medium text", "This is a medium-sized text. " * 1000),
        ("Large text", "This is a large text. " * 10000),
        ("Very large text", "This is a very large text. " * 100000),
    ]
    
    for name, text in test_cases:
        print(f"{name}:")
        print(f"  Length: {len(text):,} characters")
        estimated_tokens = estimate_token_count(text)
        print(f"  Estimated tokens: {estimated_tokens:,}")
        
        optimal_model = get_optimal_model_for_text(text)
        if optimal_model:
            config = get_model_context_config(optimal_model)
            utilization = (estimated_tokens / config.input_tokens) * 100
            print(f"  Optimal model: {optimal_model}")
            print(f"  Context utilization: {utilization:.1f}%")
        else:
            print(f"  No suitable model found")
        print()


def demo_enhanced_llm_provider():
    """Demonstrate enhanced LLM provider with automatic model selection."""
    print("=== Enhanced LLM Provider Demo ===\n")
    
    # Check if API key is available
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("ANTHROPIC_API_KEY not set. Skipping API calls.")
        print("Set the environment variable to test actual API calls.")
        return
    
    # Create enhanced provider
    provider = EnhancedLLMProvider(
        preferred_provider="claude",
        auto_model_selection=True
    )
    
    # Test with different prompt sizes
    small_prompt = "Write a simple Python function to add two numbers."
    large_prompt = "Analyze this codebase and provide comprehensive feedback. " + "Code content here. " * 50000
    
    print("Testing with small prompt:")
    print(f"  Prompt length: {len(small_prompt)} characters")
    analysis = provider.get_context_analysis(small_prompt)
    print(f"  Recommended model: {analysis['recommended_model']}")
    print(f"  Estimated tokens: {analysis['estimated_tokens']:,}")
    
    print("\nTesting with large prompt:")
    print(f"  Prompt length: {len(large_prompt)} characters")
    analysis = provider.get_context_analysis(large_prompt)
    print(f"  Recommended model: {analysis['recommended_model']}")
    print(f"  Estimated tokens: {analysis['estimated_tokens']:,}")
    
    # Show usage stats
    print("\nUsage statistics:")
    stats = provider.get_usage_stats()
    if stats:
        for model, count in stats.items():
            print(f"  {model}: {count} calls")
    else:
        print("  No API calls made yet")


def demo_large_codebase_processing():
    """Demonstrate processing large codebases."""
    print("=== Large Codebase Processing Demo ===\n")
    
    # Check if API key is available
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("ANTHROPIC_API_KEY not set. Skipping API calls.")
        return
    
    # Create enhanced provider
    provider = EnhancedLLMProvider(
        preferred_provider="claude",
        auto_model_selection=True
    )
    
    # Example: Process the current project
    project_path = Path(__file__).parent.parent
    
    print(f"Analyzing project at: {project_path}")
    
    # Collect Python files
    python_files = list(project_path.rglob("*.py"))
    print(f"Found {len(python_files)} Python files")
    
    # Estimate total project size
    total_content = ""
    for file_path in python_files[:10]:  # Limit to first 10 files for demo
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                total_content += f"\n# {file_path}\n{content}\n"
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
    
    print(f"Total content length: {len(total_content):,} characters")
    estimated_tokens = estimate_token_count(total_content)
    print(f"Estimated tokens: {estimated_tokens:,}")
    
    # Check if it fits in the 1M context window
    can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", total_content)
    print(f"Fits in 1M context window: {can_fit}")
    
    if can_fit:
        print("This codebase can be processed in a single API call!")
    else:
        print("This codebase would need to be processed in chunks.")


def demo_verification_use_cases():
    """Demonstrate verification-specific use cases for large context."""
    print("=== Verification Use Cases Demo ===\n")
    
    # Example 1: Large specification file
    large_spec = """
# Large Lean 4 specification file
theorem large_verification_example (n : Nat) : n + 0 = n := by
  -- This is a large verification task that benefits from context
  -- The model can see the entire specification and related lemmas
  """ + "\n".join([f"  -- Lemma {i}: Some mathematical property" for i in range(1000)])
    
    print("Example 1: Large specification file")
    print(f"  Length: {len(large_spec):,} characters")
    estimated_tokens = estimate_token_count(large_spec)
    print(f"  Estimated tokens: {estimated_tokens:,}")
    
    optimal_model = get_optimal_model_for_text(large_spec)
    if optimal_model:
        config = get_model_context_config(optimal_model)
        utilization = (estimated_tokens / config.input_tokens) * 100
        print(f"  Optimal model: {optimal_model}")
        print(f"  Context utilization: {utilization:.1f}%")
    
    # Example 2: Multiple related files
    multi_file_content = """
# Multiple related verification files
# File 1: Basic definitions
# File 2: Intermediate lemmas  
# File 3: Main theorem
# File 4: Supporting proofs
""" + "\n".join([f"# File {i}: Additional context and definitions" for i in range(5, 100)])
    
    print("\nExample 2: Multiple related files")
    print(f"  Length: {len(multi_file_content):,} characters")
    estimated_tokens = estimate_token_count(multi_file_content)
    print(f"  Estimated tokens: {estimated_tokens:,}")
    
    optimal_model = get_optimal_model_for_text(multi_file_content)
    if optimal_model:
        config = get_model_context_config(optimal_model)
        utilization = (estimated_tokens / config.input_tokens) * 100
        print(f"  Optimal model: {optimal_model}")
        print(f"  Context utilization: {utilization:.1f}%")
    
    print()


def main():
    """Run all demonstrations."""
    print("Claude 3.5 Sonnet 1M Token Context Window Demo")
    print("=" * 50)
    print()
    
    # Run demonstrations
    demo_context_window_analysis()
    demo_optimal_model_selection()
    demo_enhanced_llm_provider()
    demo_large_codebase_processing()
    demo_verification_use_cases()
    
    print("Demo completed!")
    print("\nKey benefits of 1M token context window:")
    print("1. Process entire codebases in single API calls")
    print("2. Maintain full context across multiple files")
    print("3. Handle complex verification tasks with all dependencies")
    print("4. Reduce API calls and improve consistency")
    print("5. Enable more sophisticated code analysis and generation")


if __name__ == "__main__":
    main()




