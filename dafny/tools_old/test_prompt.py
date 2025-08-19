#!/usr/bin/env python3

from prompt_loader import PromptLoader

def test_prompt():
    pl = PromptLoader()
    
    with open('benchmarks/dafny-bench_specs/simple_specs/dafny-synthesis_task_id_606_DegreesToRadians.dfy', 'r') as f:
        code = f.read()
    
    prompt = pl.format_prompt('generate_code', code=code)
    
    print('PROMPT LENGTH:', len(prompt))
    print('PROMPT PREVIEW:')
    print('=' * 50)
    print(prompt[:1000] + '...' if len(prompt) > 1000 else prompt)
    print('=' * 50)
    
    # Check if the prompt contains the expected format
    if '// SPEC' in prompt:
        print("✅ Prompt contains // SPEC format")
    else:
        print("❌ Prompt missing // SPEC format")
    
    if '//IMPL' in prompt:
        print("✅ Prompt contains //IMPL format")
    else:
        print("❌ Prompt missing //IMPL format")

if __name__ == "__main__":
    test_prompt() 