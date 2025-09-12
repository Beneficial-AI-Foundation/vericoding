#!/usr/bin/env python3
"""
Generate verified code from Hoare specifications - Direct approach.
This script uses a more direct prompt to generate code immediately.
"""

import os
import sys
import re
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


def create_direct_code_generation_prompt(specs: Dict[str, str]) -> str:
    """Create a direct prompt that generates code immediately."""
    
    # Combine all specifications
    all_specs_content = ""
    for filename, content in specs.items():
        all_specs_content += f"\n# {filename}\n```lean\n{content}\n```\n"
    
    prompt = f"""
# Generate Verified Lean 4 Implementations

You are a Lean 4 expert. Generate complete, verified implementations for the following specifications.

## Instructions

1. **Generate code immediately** - Do not ask questions or request clarification
2. **Use constructive proofs** - Focus on executable, compilable code
3. **Include all necessary imports** - Use Std.Do.Triple and other required libraries
4. **Provide complete implementations** - All functions, lemmas, and proofs
5. **Use Lean 4 tactics** - simp, omega, rw, etc. for automation
6. **Handle preconditions** - Use the ⦃⌜condition⌝⦄ notation appropriately
7. **Be consistent** - Use similar patterns across all implementations

## Specifications

{all_specs_content}

## Output Format

For each specification, provide:

```lean
-- Implementation for: [filename]
-- Generated: [timestamp]

import Std.Do.Triple
import Std.Tactic.Do
-- Add other necessary imports

-- Complete implementation with all functions, lemmas, and proofs
-- Use constructive proofs and Lean 4 tactics
-- Ensure all specifications are satisfied

-- End of implementation
```

## Requirements

- Generate ALL {len(specs)} implementations
- Use executable, constructive proofs
- Include comprehensive verification
- Handle edge cases and error conditions
- Optimize for correctness and clarity
- Use Lean 4 best practices

## Start Generating

Begin generating the complete implementations now. Do not ask questions - just generate the code.
"""

    return prompt


def parse_generated_code(response: str) -> Dict[str, str]:
    """Parse the generated code response into individual files."""
    
    generated_files = {}
    
    # Look for code blocks with file headers
    pattern = r'-- Implementation for: (.+?)\n-- Generated: (.+?)\n\n```lean\n(.*?)\n```'
    matches = re.findall(pattern, response, re.DOTALL)
    
    print(f"Found {len(matches)} code blocks in response")
    
    for match in matches:
        filename, timestamp, code = match
        filename = filename.strip()
        code = code.strip()
        
        if filename and code:
            generated_files[filename] = code
            print(f"  ✅ Parsed: {filename} ({len(code)} characters)")
    
    # If regex didn't work, try simpler parsing
    if not generated_files:
        print("Regex parsing failed, trying simple parsing...")
        lines = response.split('\n')
        current_file = None
        current_content = []
        in_code_block = False
        
        for line in lines:
            if line.startswith('-- Implementation for:'):
                # Save previous file if exists
                if current_file and current_content:
                    generated_files[current_file] = '\n'.join(current_content)
                
                # Start new file
                current_file = line.split(':', 1)[1].strip()
                current_content = []
                in_code_block = False
            elif line.startswith('```lean'):
                in_code_block = True
                current_content = []
            elif line.startswith('```') and in_code_block:
                in_code_block = False
            elif in_code_block or (current_file and line.strip()):
                current_content.append(line)
        
        # Save last file
        if current_file and current_content:
            generated_files[current_file] = '\n'.join(current_content)
    
    return generated_files


def save_generated_code(generated_files: Dict[str, str], output_dir: str = "generated_hoare_code"):
    """Save generated code to individual files."""
    
    output_path = Path(output_dir)
    output_path.mkdir(exist_ok=True)
    
    print(f"\nSaving generated code to: {output_path.absolute()}")
    
    saved_files = []
    for filename, content in generated_files.items():
        # Clean filename
        clean_filename = filename.replace(' ', '_').replace('/', '_')
        if not clean_filename.endswith('.lean'):
            clean_filename += '.lean'
        
        file_path = output_path / clean_filename
        
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            saved_files.append(clean_filename)
            print(f"  ✅ Saved: {clean_filename}")
        except Exception as e:
            print(f"  ❌ Error saving {clean_filename}: {e}")
    
    return saved_files


def generate_code_direct(specs: Dict[str, str]) -> Dict[str, str]:
    """Generate verified code using a direct approach."""
    
    print(f"\n=== Generating Code Directly from {len(specs)} Specifications ===\n")
    
    # Check if API key is available
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("ANTHROPIC_API_KEY not set. Cannot generate code without API access.")
        return {}
    
    # Create enhanced provider
    provider = EnhancedLLMProvider(
        preferred_provider="claude",
        auto_model_selection=True
    )
    
    # Create the direct generation prompt
    prompt = create_direct_code_generation_prompt(specs)
    
    # Analyze context requirements
    estimated_tokens = estimate_token_count(prompt)
    print(f"Generation prompt: {estimated_tokens:,} tokens")
    
    # Check if it fits in 1M context
    can_fit = can_fit_in_context("claude-3-5-sonnet-20241022", prompt)
    print(f"Fits in 1M context: {'✅' if can_fit else '❌'}")
    
    if not can_fit:
        print("❌ Prompt too large for 1M context.")
        return {}
    
    print(f"\n🚀 Generating verified code for all {len(specs)} specifications...")
    print("Using direct approach - no questions, just code generation.")
    
    try:
        # Make the API call to generate code
        response = provider.call_api_with_context_optimization(prompt)
        
        print(f"\n✅ Successfully generated code!")
        print(f"Response length: {len(response):,} characters")
        
        # Parse the response into individual files
        generated_files = parse_generated_code(response)
        
        if generated_files:
            # Save to files
            saved_files = save_generated_code(generated_files)
            
            print(f"\n📊 Generation Summary:")
            print(f"  Specifications processed: {len(specs)}")
            print(f"  Code blocks generated: {len(generated_files)}")
            print(f"  Files saved: {len(saved_files)}")
            print(f"  Output directory: {Path('generated_hoare_code').absolute()}")
            
            return generated_files
        else:
            print(f"\n❌ No code blocks found in response")
            print(f"Response preview:")
            print(response[:2000] + "..." if len(response) > 2000 else response)
            return {}
        
    except Exception as e:
        print(f"❌ Error generating code: {e}")
        return {}


def main():
    """Main function to generate code directly."""
    
    print("Generate Hoare Code - Direct Approach")
    print("Using Claude 3.5 Sonnet 1M Token Context Window")
    print("=" * 60)
    
    # Collect specifications
    specs = collect_hoare_specs()
    if not specs:
        print("No specifications found. Please ensure hoare_specs_100 directory exists.")
        return
    
    # Analyze context requirements
    prompt = create_direct_code_generation_prompt(specs)
    estimated_tokens = estimate_token_count(prompt)
    
    print(f"\nContext Analysis:")
    print(f"  Total specifications: {len(specs)}")
    print(f"  Estimated tokens: {estimated_tokens:,}")
    print(f"  Fits in 1M context: {'✅' if can_fit_in_context('claude-3-5-sonnet-20241022', prompt) else '❌'}")
    
    # Generate code directly
    if os.getenv("ANTHROPIC_API_KEY"):
        print(f"\n🎯 Generating ALL {len(specs)} specifications in single API call...")
        generated_files = generate_code_direct(specs)
        
        if generated_files:
            print(f"\n🎉 Code Generation Complete!")
            print(f"Generated {len(generated_files)} implementation files")
            print(f"Files saved to: generated_hoare_code/")
        else:
            print(f"\n❌ No code was generated.")
    else:
        print(f"\n🔑 Set ANTHROPIC_API_KEY to test actual code generation")
        print(f"This would generate verified code for all {len(specs)} specifications!")


if __name__ == "__main__":
    main()
