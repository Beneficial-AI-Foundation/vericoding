#!/usr/bin/env python3
"""
Lean Specification-to-Code Processing with Claude Code SDK and MCP integration.

This module uses the Claude Code SDK to interact with Claude through the 
`claude` CLI, which can leverage MCP tools configured in .mcp.json.
"""

import os
import sys
import json
import re
import subprocess
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional, List, Tuple
from claude_code_sdk import ClaudeCodeSession, ClaudeCodeMessage

from vericoding.lean.prompt_loader import PromptLoader
from vericoding.common.prompt_loader import BasePromptLoader
from vericoding.tools.trace_logger import get_trace_logger, ConversationTrace
from vericoding.lean.claude_session_wrapper import create_tracked_session


class MCPEnhancedPromptLoader(PromptLoader):
    """Enhanced prompt loader that includes CLAUDE.md context."""
    
    def __init__(self, prompts_file=None):
        super().__init__(prompts_file)
        self.claude_md_content = self.load_claude_md()
    
    def format_prompt_with_context(self, prompt_name: str, **kwargs) -> str:
        """Format prompt with CLAUDE.md context included."""
        base_prompt = self.format_prompt(prompt_name, **kwargs)
        
        if self.claude_md_content:
            # Prepend CLAUDE.md context to the prompt
            context_header = (
                "# Project Context (from CLAUDE.md)\n\n"
                f"{self.claude_md_content}\n\n"
                "---\n\n"
                "# Task\n\n"
            )
            return context_header + base_prompt
        
        return base_prompt


def extract_lean_code(output: str) -> str:
    """Extract Lean code from Claude's response."""
    # Look for code blocks marked with ```lean
    lean_code_pattern = r'```lean\s*\n(.*?)\n```'
    match = re.search(lean_code_pattern, output, re.DOTALL)
    
    if match:
        return match.group(1).strip()
    
    # If no ```lean block found, look for any code block
    code_pattern = r'```\s*\n(.*?)\n```'
    match = re.search(code_pattern, output, re.DOTALL)
    
    if match:
        return match.group(1).strip()
    
    # If no code blocks found, return the original output
    print("Warning: Could not extract Lean code from response, using raw output")
    return output.strip()


def verify_lean_file_with_mcp(file_path: Path, session: ClaudeCodeSession) -> Tuple[bool, str]:
    """
    Verify a Lean file using MCP tools through Claude Code SDK.
    
    Returns:
        Tuple of (success, output)
    """
    # First check if file exists
    if not file_path.exists():
        return False, f"File not found: {file_path}"
    
    # Use Claude to analyze the file with MCP tools
    verification_prompt = f"""
Please verify this Lean file using the lean-lsp-mcp tools:

File: {file_path}

Use the following tools:
1. lean_file_contents to read the file
2. lean_diagnostic_messages to get all diagnostic messages
3. lean_build if needed

Report whether the file verifies successfully and list any errors or warnings.
"""
    
    response = session.send_message(verification_prompt)
    
    # Parse response to determine success
    response_text = response.text.lower()
    
    # Check for success indicators
    if ("no errors" in response_text or 
        "successfully verified" in response_text or
        "verification successful" in response_text):
        return True, response.text
    
    # Check for error indicators
    if ("error" in response_text or 
        "failed" in response_text or
        "cannot" in response_text):
        return False, response.text
    
    # Fallback to traditional verification
    try:
        result = subprocess.run(["lean", str(file_path)], 
                              capture_output=True, text=True, timeout=120)
        return result.returncode == 0, result.stdout + '\n' + result.stderr
    except Exception as e:
        return False, str(e)


def process_spec_file_with_mcp(file_path: Path, 
                              max_iterations: int = 5,
                              use_mcp_verification: bool = True,
                              enable_trace: bool = True) -> Dict:
    """
    Process a Lean specification file using Claude Code SDK with MCP tools.
    
    Args:
        file_path: Path to the Lean specification file
        max_iterations: Maximum number of fix attempts
        use_mcp_verification: Whether to use MCP for verification
    
    Returns:
        Dictionary with results
    """
    base_file_name = file_path.stem
    output_dir = file_path.parent / f"mcp_output_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    output_dir.mkdir(exist_ok=True)
    
    print(f"Processing {file_path.name} with MCP tools...")
    
    # Initialize prompt loader with CLAUDE.md context
    prompt_loader = MCPEnhancedPromptLoader()
    
    # Read the original file
    with open(file_path, 'r', encoding='utf-8') as f:
        original_code = f.read()
    
    # Generate experiment ID
    experiment_id = f"{base_file_name}_{datetime.now().strftime('%Y%m%d_%H%M%S%f')}"
    
    # Initialize Claude Code session with tracing
    if enable_trace:
        session = create_tracked_session(
            experiment_id=experiment_id,
            file_name=file_path.name,
            language="lean",
            use_mcp=True,
            metadata={
                "max_iterations": max_iterations,
                "use_mcp_verification": use_mcp_verification,
                "original_code_length": len(original_code)
            }
        )
        trace_logger = get_trace_logger()
    else:
        session = ClaudeCodeSession()
        trace_logger = None
    
    # Generate initial implementation
    print("  Generating initial implementation with MCP context...")
    
    generate_prompt = prompt_loader.format_prompt_with_context(
        "generate_code",
        code=original_code
    )
    
    # Add MCP-specific instructions
    mcp_prompt = f"""
You have access to lean-lsp-mcp tools. Use them to:
1. Understand the proof state with lean_goal
2. Get hover information with lean_hover_info
3. Search for relevant theorems with lean_leansearch and lean_loogle
4. Check diagnostics with lean_diagnostic_messages

{generate_prompt}

Use the MCP tools actively during implementation to make informed decisions.
"""
    
    response = session.send_message(mcp_prompt)
    generated_code = extract_lean_code(response.text)
    
    # Save initial generated code
    initial_file = output_dir / f"{base_file_name}_initial.lean"
    with open(initial_file, 'w', encoding='utf-8') as f:
        f.write(generated_code)
    
    # Iterative refinement
    current_code = generated_code
    success = False
    last_error = None
    
    for iteration in range(1, max_iterations + 1):
        print(f"  Iteration {iteration}/{max_iterations}: Verifying...")
        
        # Write current code to file
        temp_file = output_dir / f"{base_file_name}_iter{iteration}.lean"
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(current_code)
        
        # Verify
        if use_mcp_verification:
            verified, output = verify_lean_file_with_mcp(temp_file, session)
        else:
            # Fallback to standard verification
            try:
                result = subprocess.run(["lean", str(temp_file)], 
                                      capture_output=True, text=True, timeout=120)
                verified = result.returncode == 0
                output = result.stdout + '\n' + result.stderr
            except Exception as e:
                verified = False
                output = str(e)
        
        # Log verification result
        if trace_logger:
            trace_logger.add_verification_result(
                experiment_id=experiment_id,
                iteration=iteration,
                success=verified,
                output=output,
                metadata={"code_length": len(current_code)}
            )
        
        if verified:
            print(f"    ✓ Verification successful!")
            success = True
            break
        else:
            print(f"    ✗ Verification failed")
            last_error = output
            
            if iteration < max_iterations:
                print("    Attempting to fix with MCP tools...")
                
                fix_prompt = f"""
The Lean code has verification errors. Use the MCP tools to understand and fix the issues:

Current code:
```lean
{current_code}
```

Error output:
{output}

Use these MCP tools to fix the issues:
1. lean_goal to understand the proof state at error locations
2. lean_hover_info to get documentation about unfamiliar terms
3. lean_leansearch or lean_loogle to find relevant theorems
4. lean_completions to find available tactics or terms
5. lean_state_search to find theorems based on the current proof state

Provide the fixed code.
"""
                
                fix_response = session.send_message(fix_prompt)
                current_code = extract_lean_code(fix_response.text)
    
    # Save final implementation
    final_file = output_dir / f"{base_file_name}_final.lean"
    with open(final_file, 'w', encoding='utf-8') as f:
        f.write(current_code)
    
    # Finalize trace
    trace_file = None
    if trace_logger:
        trace_logger.set_final_code(experiment_id, current_code)
        trace = trace_logger.end_trace(experiment_id, save=True)
        
        # Also save a markdown report
        report = trace_logger.create_markdown_report(trace)
        report_file = output_dir / f"{base_file_name}_trace_report.md"
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        trace_file = str(report_file)
        print(f"  Trace report saved to {report_file}")
    
    return {
        "success": success,
        "file": file_path.name,
        "output": str(final_file),
        "iterations": iteration,
        "error": None if success else last_error,
        "output_dir": str(output_dir),
        "trace_file": trace_file,
        "experiment_id": experiment_id
    }


def run_mcp_experiment(spec_dir: Path, max_files: Optional[int] = None) -> List[Dict]:
    """
    Run MCP-enhanced processing on a directory of Lean files.
    
    Args:
        spec_dir: Directory containing Lean specification files
        max_files: Maximum number of files to process (for testing)
    
    Returns:
        List of results
    """
    from vericoding.lean.spec_to_code_lean import find_lean_files_with_sorry
    
    files = find_lean_files_with_sorry(spec_dir)
    if max_files:
        files = files[:max_files]
    
    if not files:
        print(f"No Lean files with 'sorry' found in {spec_dir}")
        return []
    
    print(f"Found {len(files)} Lean files to process with MCP")
    
    results = []
    for i, file_path in enumerate(files, 1):
        print(f"\n[{i}/{len(files)}] Processing {file_path.name}...")
        
        try:
            result = process_spec_file_with_mcp(file_path)
            results.append(result)
            
            # Add delay to avoid rate limiting
            time.sleep(2)
            
        except Exception as e:
            print(f"  Error processing {file_path.name}: {e}")
            results.append({
                "success": False,
                "file": file_path.name,
                "output": None,
                "iterations": 0,
                "error": str(e)
            })
    
    # Print summary
    successful = sum(1 for r in results if r["success"])
    print(f"\n=== MCP Experiment Summary ===")
    print(f"Total files: {len(results)}")
    print(f"Successful: {successful}")
    print(f"Failed: {len(results) - successful}")
    print(f"Success rate: {successful / len(results) * 100:.1f}%")
    
    return results


if __name__ == "__main__":
    # Example usage
    import argparse
    
    parser = argparse.ArgumentParser(description="Lean spec-to-code with MCP tools")
    parser.add_argument("spec_dir", type=Path, help="Directory with Lean spec files")
    parser.add_argument("--max-files", type=int, help="Max files to process")
    parser.add_argument("--max-iterations", type=int, default=5, help="Max fix iterations")
    
    args = parser.parse_args()
    
    if not args.spec_dir.exists():
        print(f"Error: Directory {args.spec_dir} does not exist")
        sys.exit(1)
    
    results = run_mcp_experiment(args.spec_dir, max_files=args.max_files)
    
    # Save results
    output_file = f"mcp_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(output_file, "w") as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to {output_file}")