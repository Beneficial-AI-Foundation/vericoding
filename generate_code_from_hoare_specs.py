#!/usr/bin/env python3
"""
Generate verified code from Hoare specifications using 1M token context window.
"""

import os
import sys
from pathlib import Path
from typing import Dict, List
from datetime import datetime

# Add the project root to the path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

from vericoding.core import (
    EnhancedLLMProvider,
    estimate_token_count,
    can_fit_in_context,
)


def collect_hoare_specs(directory: str = "hoare_specs_100") -> Dict[str, str]:
    """Collect all Lean files from the hoare_specs_100 directory."""
    specs_dir = Path(directory)
    if not specs_dir.exists():
        print(f"Directory {directory} not found!")
        return {}
    
    specs = {}
    lean_files = list(specs_dir.glob("*.lean"))
    
    print(f"Found {len(lean_files)} Lean files in {directory}")
    
    for file_path in lean_files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                specs[file_path.name] = content
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
    
    return specs


def create_code_generation_prompt(specs: Dict[str, str]) -> str:
    """Create a comprehensive prompt for generating verified code from all specs."""
    
    # Combine all specifications
    all_specs_content = ""
    for filename, content in specs.items():
        all_specs_content += f"\n# {filename}\n```lean\n{content}\n```\n"
    
    prompt = f"""
# Automated Code Generation from Hoare Specifications

You have access to {len(specs)} Hoare specification files. Each file contains Lean 4 specifications that need implementation.

## Task: Generate Verified Code

For each specification, generate the complete verified implementation in Lean 4. The implementation should:

1. **Satisfy the specification exactly** - All preconditions, postconditions, and invariants must be met
2. **Be verified** - Use Lean 4's verification capabilities to prove correctness
3. **Follow best practices** - Use appropriate tactics, lemmas, and proof strategies
4. **Be efficient** - Implement algorithms that are both correct and performant

## Specifications to Implement

{all_specs_content}

## Implementation Requirements

For each specification file, provide:

1. **Complete Implementation**: All functions, methods, and data structures
2. **Verification Proofs**: All necessary lemmas, theorems, and proofs
3. **Documentation**: Clear comments explaining the implementation approach
4. **Error Handling**: Appropriate error cases and edge conditions
5. **Optimization**: Efficient algorithms where applicable

## Output Format

Provide the complete implementation for each specification in the following format:

```lean
-- Implementation for: [filename]
-- Specification: [brief description]

[complete verified implementation]

-- Verification complete
```

## Guidelines

- Use Lean 4's verification capabilities extensively
- Ensure all specifications are fully satisfied
- Provide clear, readable, and maintainable code
- Include comprehensive proofs for correctness
- Handle edge cases and error conditions
- Optimize for performance where possible

## Instructions

Generate the complete verified implementation for all {len(specs)} specifications. Each implementation should be production-ready and fully verified.
"""

    return prompt


def generate_code_from_specs(specs: Dict[str, str]) -> Dict[str, str]:
    """Generate verified code from all specifications using 1M token context."""
    
    print(f"\n=== Generating Code from {len(specs)} Specifications ===\n")
    
    # Check if API key is available
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("ANTHROPIC_API_KEY not set. Cannot generate code without API access.")
        print("This would make a single API call with all specifications to generate verified code.")
        return {}
    
    # Create enhanced provider
    provider = EnhancedLLMProvider(
        preferred_provider="claude",
        auto_model_selection=True
    )
    
    # Create the generation prompt
    prompt = create_code_generation_prompt(specs)
    
    # Analyze context requirements
    estimated_tokens = estimate_token_count(prompt)
    print(f"Generation prompt: {estimated_tokens:,} tokens")
    
    # Check if it fits in 1M context
    can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", prompt)
    print(f"Fits in 1M context: {'✅' if can_fit else '❌'}")
    
    if not can_fit:
        print("❌ Prompt too large for 1M context. Would need chunking strategy.")
        return {}
    
    print(f"\n🚀 Generating verified code for all {len(specs)} specifications...")
    print("This will make a single API call with the 1M token context window.")
    
    try:
        # Make the API call to generate code
        response = provider.call_api_with_context_optimization(prompt)
        
        print(f"\n✅ Successfully generated code!")
        print(f"Response length: {len(response):,} characters")
        
        # For demo purposes, show a sample of the response
        print(f"\nSample of generated code:")
        print(response[:1000] + "..." if len(response) > 1000 else response)
        
        return {"generated_code": response}
        
    except Exception as e:
        print(f"❌ Error generating code: {e}")
        return {}


def main():
    """Main function to generate code from Hoare specifications."""
    
    print("Automated Code Generation from Hoare Specifications")
    print("Using Claude 3.5 Sonnet 1M Token Context Window")
    print("=" * 70)
    
    # Collect specifications
    specs = collect_hoare_specs()
    if not specs:
        print("No specifications found. Please ensure hoare_specs_100 directory exists.")
        return
    
    # Analyze context requirements
    prompt = create_code_generation_prompt(specs)
    estimated_tokens = estimate_token_count(prompt)
    
    print(f"\nContext Analysis:")
    print(f"  Total specifications: {len(specs)}")
    print(f"  Estimated tokens: {estimated_tokens:,}")
    print(f"  Fits in 1M context: {'✅' if can_fit_in_context('claude-3-5-sonnet-20241022', prompt) else '❌'}")
    
    # Generate code
    if os.getenv("ANTHROPIC_API_KEY"):
        print(f"\n🎯 Attempting to generate ALL {len(specs)} specifications in single API call...")
        generated = generate_code_from_specs(specs)
        
        if generated:
            print(f"\n🎉 Code Generation Demo Complete!")
            print(f"The 1M token context window enables:")
            print(f"1. ✅ Single API call for all {len(specs)} specifications")
            print(f"2. ✅ Comprehensive context across all files")
            print(f"3. ✅ Pattern recognition and consistency")
            print(f"4. ✅ Automated verified code generation")
    else:
        print(f"\n🔑 Set ANTHROPIC_API_KEY to test actual code generation")
        print(f"This would generate verified code for all {len(specs)} specifications in one API call!")


if __name__ == "__main__":
    main()
