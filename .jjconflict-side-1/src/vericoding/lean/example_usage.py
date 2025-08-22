#!/usr/bin/env python3
"""
Example usage of the modern Lean verification framework.
"""
from pathlib import Path
from vericoding.lean import (
    LeanAgent, 
    run_experiment, 
    run_comparison_experiment,
    run_lean_agent
)


def example_single_file():
    """Example: Process a single Lean specification file."""
    spec_file = Path("example_spec.lean")
    
    # Create a sample specification file
    spec_content = """
def add (n m : Nat) : Nat := sorry

theorem add_comm (n m : Nat) : add n m = add m n := sorry

theorem add_zero (n : Nat) : add n 0 = n := sorry
"""
    
    with open(spec_file, 'w') as f:
        f.write(spec_content)
    
    # Run the agent
    print("Processing single file with MCP tools...")
    summary = run_lean_agent(spec_file, use_mcp=True, max_iterations=3)
    print(f"Result: {summary}")
    
    # Clean up
    spec_file.unlink(missing_ok=True)
    Path(f"{spec_file.stem}_impl.lean").unlink(missing_ok=True)


def example_experiment():
    """Example: Run a full experiment on a directory."""
    spec_dir = Path("./lean_specs")
    
    # Run experiment with MCP tools
    print("Running experiment with MCP tools...")
    summary = run_experiment(
        spec_dir=spec_dir,
        name="test_mcp_experiment",
        use_mcp=True,
        max_files=5  # Limit for demo
    )
    
    return summary


def example_comparison():
    """Example: Compare baseline vs MCP performance."""
    spec_dir = Path("./lean_specs")
    
    # Run comparison experiment
    print("Running comparison experiment...")
    comparison = run_comparison_experiment(
        spec_dir=spec_dir,
        max_files=3  # Small number for demo
    )
    
    return comparison


def example_custom_agent():
    """Example: Using the LeanAgent directly for custom workflows."""
    from vericoding.lean import LeanAgent
    
    # Create agent with custom configuration
    agent = LeanAgent(use_mcp=True, max_iterations=5)
    
    # Custom spec
    spec_code = """
def factorial (n : Nat) : Nat := sorry

theorem factorial_zero : factorial 0 = 1 := sorry

theorem factorial_succ (n : Nat) : factorial (n + 1) = (n + 1) * factorial n := sorry
"""
    
    # Generate code
    generated = agent.generate_code(spec_code, iteration=0)
    print("Generated code:")
    print(generated)
    
    # You can also verify, fix, and iterate manually
    # This gives you full control over the process


def example_prompt_customization():
    """Example: Using custom prompts with Pydantic models."""
    from vericoding.lean import LeanPromptConfig, PromptType, LeanPromptManager
    from vericoding.lean.prompts import MCPTool
    
    # Create custom prompt configuration
    config = LeanPromptConfig(
        type=PromptType.GENERATE,
        code="def myFunc : Nat → Nat := sorry",
        use_mcp=True,
        mcp_tools=[
            MCPTool.LEAN_GOAL,
            MCPTool.LEAN_LEANSEARCH,
            MCPTool.LEAN_STATE_SEARCH
        ],
        iteration=0,
        temperature=0.1  # Lower temperature for more focused generation
    )
    
    # Create prompt
    manager = LeanPromptManager()
    prompt = manager.create_prompt(config)
    
    print("Custom prompt created:")
    print(prompt[:200] + "...")  # Show first 200 chars


if __name__ == "__main__":
    print("=== Lean Verification Framework Examples ===\n")
    
    # Example 1: Single file processing
    print("1. Single File Processing")
    example_single_file()
    print()
    
    # Example 2: Custom agent usage
    print("2. Custom Agent Usage")
    example_custom_agent()
    print()
    
    # Example 3: Prompt customization
    print("3. Prompt Customization")
    example_prompt_customization()
    print()
    
    # For full experiments, you would run:
    # example_experiment()
    # example_comparison()
    
    print("\nFor full experiments with WANDB tracking, set WANDB_API_KEY and run:")
    print("  python -m vericoding.lean.example_usage --experiment")
    print("  python -m vericoding.lean.example_usage --comparison")