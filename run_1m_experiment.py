#!/usr/bin/env python3
"""
Helper script to run 1M token experiments with wandb integration.
"""

import os
import subprocess
import sys
from pathlib import Path

def check_environment():
    """Check if required environment variables are set."""
    print("🔍 Checking environment...")
    
    # Check API keys
    anthropic_key = os.getenv("ANTHROPIC_API_KEY")
    wandb_key = os.getenv("WANDB_API_KEY")
    
    print(f"  ANTHROPIC_API_KEY: {'✅ SET' if anthropic_key else '❌ NOT SET'}")
    print(f"  WANDB_API_KEY: {'✅ SET' if wandb_key else '❌ NOT SET'}")
    
    if not anthropic_key:
        print("\n⚠️  Please set your Anthropic API key:")
        print("   export ANTHROPIC_API_KEY='your-api-key-here'")
        return False
    
    if not wandb_key:
        print("\n⚠️  WANDB_API_KEY not set - wandb tracking will be disabled")
        print("   To enable wandb tracking, set: export WANDB_API_KEY='your-wandb-key'")
    
    return True

def check_lean_installation():
    """Check if Lean is installed and accessible."""
    print("\n🔍 Checking Lean installation...")
    
    try:
        result = subprocess.run(['lean', '--version'], 
                              capture_output=True, text=True, timeout=10)
        if result.returncode == 0:
            print(f"  ✅ Lean found: {result.stdout.strip()}")
            return True
        else:
            print(f"  ❌ Lean not working: {result.stderr}")
            return False
    except FileNotFoundError:
        print("  ❌ Lean not found in PATH")
        print("  💡 Install Lean 4 from: https://leanprover.github.io/lean4/doc/")
        return False
    except subprocess.TimeoutExpired:
        print("  ❌ Lean command timed out")
        return False

def find_hoare_specs():
    """Find the hoare_specs_100 directory."""
    print("\n🔍 Looking for hoare_specs_100 directory...")
    
    possible_paths = [
        "hoare_specs_100",
        "all_hoare_specs",
        "lean_sample_100",
        "benchmarks/verina"
    ]
    
    for path in possible_paths:
        if Path(path).exists():
            print(f"  ✅ Found: {path}")
            return path
    
    print("  ❌ No hoare_specs_100 directory found")
    print("  💡 Available directories:")
    for path in Path(".").iterdir():
        if path.is_dir() and any(keyword in path.name.lower() for keyword in ['spec', 'lean', 'hoare']):
            print(f"    - {path}")
    
    return None

def run_experiment(specs_dir: str, use_wandb: bool = True):
    """Run the 1M token experiment."""
    print(f"\n🚀 Starting 1M Token Experiment...")
    print(f"  Specs directory: {specs_dir}")
    print(f"  Wandb tracking: {'Enabled' if use_wandb else 'Disabled'}")
    
    # Build command
    cmd = [
        "python3", "spec_to_code_1m.py",
        "lean", specs_dir,
        "--batch-mode",
        "--context-aware",
        "--smart-batching",
        "--llm-model", "claude-3-5-sonnet-20241022",
        "--batch-size", "800000",
        "--debug"
    ]
    
    if not use_wandb:
        cmd.append("--no-wandb")
    
    print(f"\n📋 Command:")
    print(f"  {' '.join(cmd)}")
    
    # Ask for confirmation
    response = input("\n🤔 Proceed with experiment? (y/N): ").strip().lower()
    if response not in ['y', 'yes']:
        print("❌ Experiment cancelled")
        return
    
    print(f"\n🔄 Running experiment...")
    print("=" * 80)
    
    try:
        # Run the command
        result = subprocess.run(cmd, check=True)
        print("=" * 80)
        print("✅ Experiment completed successfully!")
        
    except subprocess.CalledProcessError as e:
        print("=" * 80)
        print(f"❌ Experiment failed with exit code {e.returncode}")
        return False
    except KeyboardInterrupt:
        print("\n❌ Experiment interrupted by user")
        return False
    
    return True

def main():
    """Main function."""
    print("🎯 1M Token Experiment Runner")
    print("=" * 50)
    
    # Check environment
    if not check_environment():
        print("\n❌ Environment not ready. Please set required API keys.")
        sys.exit(1)
    
    # Check Lean installation
    if not check_lean_installation():
        print("\n❌ Lean not properly installed. Please install Lean 4.")
        sys.exit(1)
    
    # Find specs directory
    specs_dir = find_hoare_specs()
    if not specs_dir:
        print("\n❌ No suitable specifications directory found.")
        sys.exit(1)
    
    # Check if wandb should be used
    use_wandb = bool(os.getenv("WANDB_API_KEY"))
    
    # Run experiment
    success = run_experiment(specs_dir, use_wandb)
    
    if success:
        print("\n🎉 Experiment completed!")
        print("\n📊 Next steps:")
        print("  1. Check the generated code in the output directory")
        print("  2. Review the wandb dashboard (if enabled)")
        print("  3. Analyze the results and iterate")
    else:
        print("\n💡 Troubleshooting tips:")
        print("  1. Check your API keys are correct")
        print("  2. Ensure Lean 4 is properly installed")
        print("  3. Verify the specs directory contains valid .lean files")
        print("  4. Check the error messages above for specific issues")

if __name__ == "__main__":
    main()






















