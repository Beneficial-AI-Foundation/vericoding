#!/usr/bin/env python3
"""
Quick test of wandb + lake build integration with just a few specs.
"""

import subprocess
import sys
import os
from pathlib import Path

def main():
    print("=" * 60)
    print("Testing Lake + Wandb Integration (Quick Test)")
    print("=" * 60)
    
    # Check wandb
    if not os.getenv("WANDB_API_KEY"):
        print("❌ WANDB_API_KEY not set")
        return 1
    print("✅ WANDB_API_KEY is set")
    
    # Set up environment
    env = os.environ.copy()
    env["WANDB_PROJECT"] = "vericoding-test"
    env["WANDB_MODE"] = "online"
    
    # Run on just a few Clever specs to test
    spec_dir = Path("/Users/alokbeniwal/vericoding/lean/Benchmarks/Clever/src/lean4/specs")
    
    # Create a temp dir with just 3 specs for quick testing
    import tempfile
    import shutil
    
    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir) / "test_specs"
        temp_path.mkdir()
        
        # Copy just 3 specs - find problem 1, 2, 3 specifically
        specs = []
        for num in [1, 2, 3]:
            spec_file = spec_dir / f"problem_{num}_spec.lean"
            if spec_file.exists():
                specs.append(spec_file)
        
        # If not all found, just take first 3 available
        if len(specs) < 3:
            specs = list(spec_dir.glob("problem_*_spec.lean"))[:3]
        for spec in specs:
            shutil.copy2(spec, temp_path / spec.name)
            print(f"  Testing with: {spec.name}")
        
        print("=" * 60)
        
        # Run spec_to_code
        cmd = [
            sys.executable,
            "/Users/alokbeniwal/vericoding/spec_to_code.py",
            "lean",
            str(temp_path),
            "--iterations", "1",  # Just 1 iteration for quick test
            "--workers", "2",
            "--llm-provider", "claude",
            "--llm-model", "claude-sonnet-4-20250514",
        ]
        
        print(f"Command: {' '.join(cmd)}")
        print("=" * 60)
        
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=False,
            text=True,
            check=False
        )
        
        if result.returncode == 0:
            print("\n✅ Test successful! Lake build with wandb is working.")
        else:
            print(f"\n⚠️ Test completed with return code: {result.returncode}")
        
        return result.returncode

if __name__ == "__main__":
    sys.exit(main())