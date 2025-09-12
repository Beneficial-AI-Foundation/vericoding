#!/usr/bin/env python3
"""
Generate and save verified code from Hoare specifications using 1M token context window.
This script actually saves the generated code to individual files.
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
-- Generated on: [timestamp]

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


def parse_generated_code(response: str, spec_filenames: List[str]) -> Dict[str, str]:
    """Parse the generated code response into individual files."""
    
    generated_files = {}
    
    # Look for code blocks with file headers
    pattern = r'-- Implementation for: (.+?)\n-- Specification: (.+?)\n-- Generated on: (.+?)\n\n```lean\n(.*?)\n```'
    matches = re.findall(pattern, response, re.DOTALL)
    
    print(f"Found {len(matches)} code blocks in response")
    
    for match in matches:
        filename, description, timestamp, code = match
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


def generate_and_save_code(specs: Dict[str, str]) -> Dict[str, str]:
    """Generate verified code from all specifications and save to files."""
    
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
        
        # Parse the response into individual files
        generated_files = parse_generated_code(response, list(specs.keys()))
        
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


def show_generated_files_summary(generated_files: Dict[str, str]):
    """Show a summary of what was generated."""
    
    if not generated_files:
        print("No files were generated.")
        return
    
    print(f"\n=== Generated Files Summary ===")
    print(f"Total files generated: {len(generated_files)}")
    
    # Show first few files as examples
    print(f"\nExample generated files:")
    for i, (filename, content) in enumerate(list(generated_files.items())[:3]):
        print(f"\n{i+1}. {filename}")
        print(f"   Length: {len(content)} characters")
        print(f"   Preview: {content[:200]}...")
    
    if len(generated_files) > 3:
        print(f"\n... and {len(generated_files) - 3} more files")


def main():
    """Main function to generate and save code from Hoare specifications."""
    
    print("Generate and Save Code from Hoare Specifications")
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
    
    # Generate and save code
    if os.getenv("ANTHROPIC_API_KEY"):
        print(f"\n🎯 Generating ALL {len(specs)} specifications in single API call...")
        generated_files = generate_and_save_code(specs)
        
        if generated_files:
            show_generated_files_summary(generated_files)
            
            print(f"\n🎉 Code Generation Complete!")
            print(f"The 1M token context window enabled:")
            print(f"1. ✅ Single API call for all {len(specs)} specifications")
            print(f"2. ✅ Generated {len(generated_files)} implementation files")
            print(f"3. ✅ Saved to 'generated_hoare_code' directory")
            print(f"4. ✅ Comprehensive context across all files")
        else:
            print(f"\n❌ No code was generated. Check the response above for details.")
    else:
        print(f"\n🔑 Set ANTHROPIC_API_KEY to test actual code generation")
        print(f"This would generate verified code for all {len(specs)} specifications in one API call!")
        print(f"Generated files would be saved to 'generated_hoare_code' directory")


if __name__ == "__main__":
    main()






















