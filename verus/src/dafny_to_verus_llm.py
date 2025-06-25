#!/usr/bin/env python3
import os
import requests
import re
from pathlib import Path
from typing import List, Optional

def call_claude_api(prompt: str) -> str:
    """Call Claude API with the given prompt."""
    api_key = os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        raise ValueError("ANTHROPIC_API_KEY environment variable is required")

    url = "https://api.anthropic.com/v1/messages"
    headers = {
        "Content-Type": "application/json",
        "x-api-key": api_key,
        "anthropic-version": "2023-06-01"
    }
    payload = {
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 8192,
        "messages": [{"role": "user", "content": prompt}]
    }

    response = requests.post(url, headers=headers, json=payload)
    response.raise_for_status()
    data = response.json()
    
    # Extract text from the response
    if "content" in data and len(data["content"]) > 0:
        content = data["content"][0]
        if "text" in content:
            return content["text"].strip()
        else:
            return str(content).strip()
    else:
        raise ValueError("Unexpected response format from Claude API")

def collect_dafny_specs(specs_dir: Path) -> List[tuple[Path, str]]:
    """
    Collect all Dafny specs from the given directory.
    Returns a list of tuples (file_path, spec_content).
    """
    specs = []
    for dafny_file in specs_dir.rglob("*.dfy"):
        # Skip implementation files
        if '_impl.dfy' in dafny_file.name:
            continue
            
        try:
            with open(dafny_file, 'r') as f:
                content = f.read().strip()
                if content:  # Only include non-empty files
                    specs.append((dafny_file, content))
        except Exception as e:
            print(f"Error reading {dafny_file}: {e}")
            
    return specs

def create_llm_prompt(dafny_spec: str) -> str:
    """Create a prompt for the LLM to translate Dafny to Verus."""
    return f"""Please translate the following Dafny specification to Verus syntax.
Key translation rules:
1. Dafny 'method' becomes Verus 'pub fn'
2. Dafny 'returns' becomes '->'
3. Keep requires/ensures clauses but wrap them in requires()/ensures()
4. Do not provide an implementation, just leave an empty body
5. Preserve all types and conditions exactly as they appear
6. Keep the same parameter names and types

Here is the Dafny spec:

{dafny_spec}

Please provide only the Verus translation, without any explanation or additional text."""

def extract_verus_code(llm_response: str) -> str:
    """Extract Verus code from LLM response."""
    # First try to extract from code blocks
    code_block_match = re.search(r'```(?:rust|verus)?\n(.*?)```', llm_response, re.DOTALL | re.IGNORECASE)
    if code_block_match:
        return code_block_match.group(1).strip()
    
    # If no code block, return the entire response stripped of any obvious non-code parts
    lines = llm_response.split('\n')
    code_lines = []
    for line in lines:
        # Skip lines that are clearly LLM reasoning or commentary
        if (line.strip().startswith('Looking at') or
            line.strip().startswith('Here is') or
            line.strip().startswith('The translation') or
            line.strip().startswith('1.') or
            line.strip().startswith('2.') or
            line.strip().startswith('3.') or
            line.strip().startswith('4.') or
            line.strip().startswith('5.')):
            continue
        code_lines.append(line)
    
    return '\n'.join(code_lines).strip()

def main():
    # Root directory containing Dafny specs
    specs_dir = Path("dafny/benchmarks/dafny-bench_specs")
    
    # Create output directory for translations
    output_dir = Path("src/verus_specs")
    translations_dir = output_dir / "translations"
    translations_dir.mkdir(parents=True, exist_ok=True)
    
    # Collect all specs
    specs = collect_dafny_specs(specs_dir)
    print(f"Found {len(specs)} Dafny specifications")
    
    # Process each spec
    for spec_path, spec_content in specs:
        print(f"\nProcessing {spec_path.relative_to(specs_dir)}...")
        
        # Create the prompt and call Claude
        prompt = create_llm_prompt(spec_content)
        try:
            llm_response = call_claude_api(prompt)
            verus_code = extract_verus_code(llm_response)
            
            # Save the translation
            translation_path = translations_dir / spec_path.relative_to(specs_dir).with_suffix('.rs')
            translation_path.parent.mkdir(parents=True, exist_ok=True)
            
            with open(translation_path, 'w') as f:
                f.write(verus_code)
                
            print(f"Created translation at {translation_path}")
            
        except Exception as e:
            print(f"Error processing {spec_path}: {e}")

if __name__ == "__main__":
    main() 