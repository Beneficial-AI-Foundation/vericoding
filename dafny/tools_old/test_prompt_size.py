#!/usr/bin/env python3

from prompt_loader import PromptLoader

def test_prompt_size():
    pl = PromptLoader()
    
    with open('benchmarks/bignum_specs/generated/bignums-full_simple_specs/bignums-full_ModExp.dfy', 'r') as f:
        code = f.read()
    
    prompt = pl.format_prompt('generate_code', code=code)
    
    print(f'Code length: {len(code)} characters')
    print(f'Prompt length: {len(prompt)} characters')
    print(f'Prompt length: {len(prompt)/1000:.1f}K characters')
    print(f'Estimated tokens: {len(prompt)/4:.0f} tokens')
    
    # Check if this exceeds Claude's input limit
    # Claude Sonnet 4 has a 200K token context window
    estimated_tokens = len(prompt) / 4
    if estimated_tokens > 180000:  # Leave some room for response
        print(f"WARNING: Prompt may be too large! Estimated {estimated_tokens:.0f} tokens")
    else:
        print(f"Prompt size looks reasonable: {estimated_tokens:.0f} tokens")

if __name__ == "__main__":
    test_prompt_size() 