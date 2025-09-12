#!/usr/bin/env python3
"""
YAML to Lean 4 Translation Script using Claude API

This script translates Dafny YAML specifications to Lean 4 using the Claude API.
It processes all 443 YAML files in the yaml-depsontop directory.
"""

import os
import yaml
import json
import time
import argparse
import subprocess
from pathlib import Path
from typing import Dict, List, Optional
import anthropic
from anthropic import Anthropic
from prompt_loader import PromptLoader

class YAMLToLeanTranslator:
    """Translates Dafny YAML specifications to Lean 4 using Claude API."""
    
    def __init__(self, api_key: str, model: str = None):
        self.client = Anthropic(api_key=api_key)
        self.prompt_loader = PromptLoader()
        
        # Use model from config if not specified
        self.model = model or self.prompt_loader.get_model()
        self.max_tokens = self.prompt_loader.get_max_tokens()
        self.temperature = self.prompt_loader.get_temperature()
        self.max_retries = self.prompt_loader.get_max_retries()
        self.rate_limit_delay = self.prompt_loader.get_rate_limit_delay()
        
        self.output_dir = Path("benchmarks/vericoding_lean/yaml-depsontop-translated")
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Track progress
        self.processed = 0
        self.total = 0
        self.errors = []
        
    def load_yaml_file(self, file_path: Path) -> Dict:
        """Load and parse a YAML file."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        except Exception as e:
            print(f"Error loading {file_path}: {e}")
            return {}
    
    def create_translation_prompt(self, yaml_content: Dict, filename: str) -> str:
        """Create a prompt for Claude to translate YAML to Lean using the prompt loader."""
        return self.prompt_loader.get_translation_prompt(yaml_content, filename)
    
    def translate_with_claude(self, prompt: str) -> Optional[str]:
        """Translate using Claude API with error handling and retries."""
        for attempt in range(self.max_retries):
            try:
                print(f"    Attempt {attempt + 1}/{self.max_retries}...")
                
                # Validate API key first
                if not self.client.api_key:
                    raise ValueError("API key is not set")
                
                print(f"    Sending request to Claude API (model: {self.model})...")
                response = self.client.messages.create(
                    model=self.model,
                    max_tokens=self.max_tokens,
                    temperature=self.temperature,
                    messages=[
                        {
                            "role": "user",
                            "content": prompt
                        }
                    ]
                )
                
                print(f"    Received response from Claude API...")
                
                if not response.content or not response.content[0].text:
                    raise ValueError("Empty response from Claude API")
                
                print(f"    Response length: {len(response.content[0].text)} characters")
                return response.content[0].text
                
            except anthropic.AuthenticationError as e:
                print(f"Authentication error: {e}")
                self.errors.append(f"Authentication failed: {e}")
                return None
            except anthropic.RateLimitError as e:
                print(f"Rate limit error: {e}")
                if attempt < self.max_retries - 1:
                    wait_time = 2 ** (attempt + 2)  # Longer wait for rate limits
                    print(f"Waiting {wait_time} seconds before retry...")
                    time.sleep(wait_time)
                else:
                    self.errors.append(f"Rate limit exceeded after {self.max_retries} attempts")
                    return None
            except Exception as e:
                print(f"Attempt {attempt + 1} failed: {e}")
                if attempt < self.max_retries - 1:
                    time.sleep(2 ** attempt)  # Exponential backoff
                else:
                    self.errors.append(f"Failed after {self.max_retries} attempts: {e}")
                    return None
    
    def save_lean_file(self, lean_code: str, filename: str):
        """Save the translated Lean code to a file."""
        # Convert filename from .yaml to .lean and ensure unique names
        base_name = filename.replace('.yaml', '')
        # Clean up the filename to avoid path issues
        clean_name = base_name.replace('/', '_').replace('\\', '_').replace(':', '_')
        lean_filename = f"{clean_name}.lean"
        output_path = self.output_dir / lean_filename
        
        try:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(lean_code)
            print(f"✓ Saved: {output_path}")
        except Exception as e:
            print(f"✗ Error saving {output_path}: {e}")
            self.errors.append(f"Save error for {filename}: {e}")
    
    def process_file(self, yaml_file: Path):
        """Process a single YAML file."""
        print(f"Processing: {yaml_file.name}")
        
        # Load YAML content
        print("  Loading YAML...")
        yaml_content = self.load_yaml_file(yaml_file)
        if not yaml_content:
            self.errors.append(f"Empty or invalid YAML: {yaml_file.name}")
            return
        
        # Create translation prompt
        print("  Creating prompt...")
        prompt = self.create_translation_prompt(yaml_content, yaml_file.name)
        print(f"  Prompt length: {len(prompt)} characters")
        
        # Translate with Claude
        print("  Calling Claude API...")
        lean_code = self.translate_with_claude(prompt)
        if lean_code is None:
            self.errors.append(f"Translation failed: {yaml_file.name}")
            return
        
        # Save Lean file
        print("  Saving file...")
        self.save_lean_file(lean_code, yaml_file.name)
        
        self.processed += 1
        print(f"Progress: {self.processed}/{self.total} ({self.processed/self.total*100:.1f}%)")
        
        # Rate limiting - be respectful to the API
        time.sleep(self.rate_limit_delay)
    
    def process_all_files(self, yaml_dir: Path):
        """Process all YAML files in the directory."""
        yaml_files = list(yaml_dir.glob("*.yaml"))
        self.total = len(yaml_files)
        
        print(f"Found {self.total} YAML files to translate")
        print(f"Output directory: {self.output_dir}")
        print(f"Using model: {self.model}")
        print(f"Configuration: max_tokens={self.max_tokens}, temperature={self.temperature}")
        print("Starting translation...")
        
        for i, yaml_file in enumerate(yaml_files):
            print(f"\n[{i+1}/{self.total}] ", end="")
            self.process_file(yaml_file)
        
        # Print summary
        print(f"\n=== Translation Complete ===")
        print(f"Processed: {self.processed}/{self.total}")
        print(f"Success rate: {self.processed/self.total*100:.1f}%")
        
        if self.errors:
            print(f"\nErrors ({len(self.errors)}):")
            for error in self.errors[:10]:  # Show first 10 errors
                print(f"  - {error}")
            if len(self.errors) > 10:
                print(f"  ... and {len(self.errors) - 10} more errors")



def main():
    parser = argparse.ArgumentParser(description="Translate YAML files to Lean using Claude API")
    parser.add_argument("--api-key", required=True, help="Claude API key")
    parser.add_argument("--model", help="Claude model to use (defaults to config)")
    parser.add_argument("--yaml-dir", default="benchmarks/dafny/dafnybench/yaml-depsontop", 
                       help="Directory containing YAML files")
    parser.add_argument("--limit", type=int, help="Limit number of files to process (for testing)")
    
    args = parser.parse_args()
    
    # Validate API key
    if not args.api_key:
        print("Error: API key is required")
        print("Usage: python translate_yaml_to_lean.py --api-key YOUR_API_KEY")
        return
    
    # Test API key validity
    try:
        test_client = Anthropic(api_key=args.api_key)
        # Try a simple API call to validate the key
        response = test_client.messages.create(
            model=args.model or "claude-3-5-sonnet-20241022",
            max_tokens=10,
            messages=[{"role": "user", "content": "Hello"}]
        )
        print(f"✓ API key validated successfully with model: {args.model or 'default'}")
    except Exception as e:
        print(f"✗ API key validation failed: {e}")
        print("Please check your API key and try again.")
        return
    
    # Check if YAML directory exists
    yaml_dir = Path(args.yaml_dir)
    if not yaml_dir.exists():
        print(f"Error: YAML directory {yaml_dir} does not exist")
        return
    
    # Create translator
    translator = YAMLToLeanTranslator(args.api_key, args.model)
    
    # Process files
    yaml_files = list(yaml_dir.glob("*.yaml"))
    if args.limit:
        yaml_files = yaml_files[:args.limit]
        print(f"Limited to {args.limit} files for testing")
    
    translator.total = len(yaml_files)
    translator.process_all_files(yaml_dir)

if __name__ == "__main__":
    main()
