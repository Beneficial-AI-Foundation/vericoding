#!/usr/bin/env python3
"""Demo of wandb integration with failure analysis for vericoding."""

import os
import sys
import time
from pathlib import Path

# Add parent directory to path
sys.path.append(str(Path(__file__).parent.parent))

import wandb
from vericoding.analysis import FailureCollector, FailureAnalyzer


def demo_failure_collection():
    """Demonstrate failure collection and analysis workflow."""
    
    # Initialize wandb if API key is set
    if not os.getenv("WANDB_API_KEY"):
        print("Set WANDB_API_KEY to enable wandb tracking")
        print("Running in demo mode without wandb...")
        return demo_without_wandb()
    
    # Initialize wandb run
    run = wandb.init(
        project=os.getenv("WANDB_PROJECT", "vericoding"),
        name=f"analysis_demo_{int(time.time())}",
        config={
            "demo": True,
            "language": "lean",
            "purpose": "failure_analysis"
        }
    )
    
    print(f"Started wandb run: {run.name}")
    print(f"View at: {run.url}")
    
    # Create failure collector
    collector = FailureCollector(run_name=run.name)
    
    # Simulate some verification failures
    test_failures = [
        {
            "file": "theorem1.lean",
            "iteration": 1,
            "spec": "theorem add_comm (a b : Nat) : a + b = b + a",
            "code": "theorem add_comm (a b : Nat) : a + b = b + a := sorry",
            "error": "Type mismatch: expected proof, got sorry"
        },
        {
            "file": "theorem1.lean",
            "iteration": 2,
            "spec": "theorem add_comm (a b : Nat) : a + b = b + a",
            "code": "theorem add_comm (a b : Nat) : a + b = b + a := by simp",
            "error": "simp made no progress"
        },
        {
            "file": "lemma_chain.lean",
            "iteration": 1,
            "spec": "lemma helper : ∀ n : Nat, n ≤ n + 1",
            "code": "lemma helper : ∀ n : Nat, n ≤ n + 1 := fun n => sorry",
            "error": "Incomplete proof: sorry is not allowed"
        },
        {
            "file": "induction.lean",
            "iteration": 3,
            "spec": "theorem nat_ind (P : Nat → Prop)",
            "code": "theorem nat_ind (P : Nat → Prop) := by induction",
            "error": "Tactic 'induction' failed: no induction variable specified"
        }
    ]
    
    # Add failures to collector
    for failure in test_failures:
        collector.add_failure(
            file_path=f"specs/{failure['file']}",
            iteration=failure["iteration"],
            spec_code=failure["spec"],
            generated_code=failure["code"],
            error_msg=failure["error"],
            proof_state="[Proof state would be captured from Lean]"
        )
        
        # Log individual metrics
        file_key = Path(failure["file"]).stem
        wandb.log({
            f"verify/{file_key}/iter": failure["iteration"],
            f"verify/{file_key}/success": 0,
            "failure_count": 1
        })
    
    # Log collected failures to wandb
    collector.log_to_wandb()
    
    # Get and display summary
    summary = collector.get_failure_summary()
    print("\n=== Failure Summary ===")
    print(f"Total failures: {summary['total_failures']}")
    print(f"Error categories: {summary['error_categories']}")
    print(f"Most problematic files: {summary['most_problematic_files']}")
    
    # Save for offline analysis
    collector.save_to_json(Path("failure_analysis.json"))
    
    # Finish run
    wandb.finish()
    print(f"\nRun completed. View at: {run.url}")
    
    # Now demonstrate post-hoc analysis
    print("\n=== Running Post-Hoc Analysis ===")
    analyzer = FailureAnalyzer()
    
    try:
        # Analyze the run we just created
        analysis = analyzer.analyze_run(run.id)
        
        # Generate improvement report
        report = analyzer.generate_improvement_report(analysis)
        print("\n" + report)
        
        # Save report
        with open("analysis_report.md", "w") as f:
            f.write(report)
        print("\nAnalysis report saved to analysis_report.md")
        
    except Exception as e:
        print(f"Analysis failed: {e}")
        print("(This is expected if running for the first time)")


def demo_without_wandb():
    """Demo workflow without wandb (offline mode)."""
    print("\n=== Running Offline Demo ===")
    
    # Create failure collector
    collector = FailureCollector(run_name="offline_demo")
    
    # Add some sample failures
    collector.add_failure(
        file_path="test.lean",
        iteration=1,
        spec_code="theorem test : 1 + 1 = 2",
        generated_code="theorem test : 1 + 1 = 2 := sorry",
        error_msg="Incomplete proof"
    )
    
    # Get summary
    summary = collector.get_failure_summary()
    print(f"Collected {summary['total_failures']} failures")
    
    # Save to JSON
    collector.save_to_json(Path("offline_failures.json"))
    print("Failures saved to offline_failures.json")
    
    # Load and analyze
    loaded = FailureCollector.load_from_json(Path("offline_failures.json"))
    print(f"Loaded {len(loaded.failures)} failures from JSON")


def demo_cross_run_analysis():
    """Demonstrate analyzing patterns across multiple runs."""
    if not os.getenv("WANDB_API_KEY"):
        print("Cross-run analysis requires WANDB_API_KEY")
        return
    
    analyzer = FailureAnalyzer()
    
    try:
        # Analyze patterns across recent runs
        patterns = analyzer.analyze_cross_run_patterns(last_n_runs=5)
        
        print("\n=== Cross-Run Analysis ===")
        print(f"Runs analyzed: {patterns.get('total_runs_analyzed', 0)}")
        print(f"Total failures: {patterns.get('total_failures', 0)}")
        print(f"Average success rate: {patterns.get('avg_success_rate', 0):.1%}")
        
        if patterns.get("consistently_failing_files"):
            print("\nFiles that consistently fail:")
            for file, rate in patterns["consistently_failing_files"].items():
                print(f"  - {file}: fails in {rate:.0%} of runs")
        
    except Exception as e:
        print(f"Cross-run analysis failed: {e}")


if __name__ == "__main__":
    print("=== W&B Failure Analysis Demo ===\n")
    
    # Run main demo
    demo_failure_collection()
    
    # Optionally run cross-run analysis
    if "--cross-run" in sys.argv:
        demo_cross_run_analysis()