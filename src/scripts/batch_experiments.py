#!/usr/bin/env python3
"""
Batch experiment runner for vericoding.

Runs experiments on the Cartesian product of all models and datasets,
calculates estimated costs and time based on initial runs.
"""

import os
import subprocess
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, List


@dataclass
class ModelConfig:
    """Configuration for an LLM model."""
    name: str
    provider: str
    input_cost_per_million: float  # USD per million input tokens
    output_cost_per_million: float  # USD per million output tokens


@dataclass  
class DatasetConfig:
    """Configuration for a dataset."""
    name: str
    path: str
    file_count: int


@dataclass
class BaselineRun:
    """Baseline performance data from initial runs."""
    files: int
    time_seconds: int
    input_tokens: int
    output_tokens: int


# Model configurations with pricing from OpenRouter
MODELS = [
    ModelConfig("claude-opus", "claude-opus", 15.0, 75.0),
    ModelConfig("claude-sonnet", "claude-sonnet", 3.0, 15.0),
    ModelConfig("deepseek", "deepseek", 0.25, 1.0),
    ModelConfig("gemini-pro", "gemini", 1.25, 10.0),
    ModelConfig("gemini-flash", "gemini-flash", 0.30, 2.50),
    ModelConfig("glm", "glm", 0.413, 1.65),
    ModelConfig("gpt", "gpt", 1.25, 10.0),  # GPT-5
    ModelConfig("gpt-mini", "gpt-mini", 0.25, 2.0),  # GPT-5-mini
    ModelConfig("grok", "grok", 3.0, 15.0),  # Grok-4
    ModelConfig("grok-code", "grok-code", 0.20, 1.50),  # Grok-code-fast-1
]

# Dataset configurations
DATASETS = [
    DatasetConfig("dafnybench", "benchmarks/lean/dafnybench/poor/unformatted", 70),
    DatasetConfig("apps", "benchmarks/lean/apps/files", 4006),
    DatasetConfig("bignum", "benchmarks/lean/bignum/poor/bignum_ob", 6),
    DatasetConfig("humaneval", "benchmarks/lean/humaneval/files", 161),
    DatasetConfig("numpy_simple", "benchmarks/lean/numpy_simple/poor/unformatted", 50),
    DatasetConfig("numpy_triple", "benchmarks/lean/numpy_triple/files", 603),
    DatasetConfig("verina", "benchmarks/lean/verina/files", 189),
]

# Baseline performance data from initial runs
BASELINE_RUNS = [
    BaselineRun(files=10, time_seconds=250, input_tokens=174041, output_tokens=39171),
    BaselineRun(files=20, time_seconds=403, input_tokens=345741, output_tokens=72026),
]


def calculate_baseline_metrics() -> tuple[float, float, float]:
    """Calculate average time per file and tokens per file from baseline runs."""
    total_files = sum(run.files for run in BASELINE_RUNS)
    total_time = sum(run.time_seconds for run in BASELINE_RUNS)
    total_input_tokens = sum(run.input_tokens for run in BASELINE_RUNS)
    total_output_tokens = sum(run.output_tokens for run in BASELINE_RUNS)
    
    time_per_file = total_time / total_files
    input_tokens_per_file = total_input_tokens / total_files
    output_tokens_per_file = total_output_tokens / total_files
    
    return time_per_file, input_tokens_per_file, output_tokens_per_file


def estimate_cost(model: ModelConfig, files: int, input_tokens_per_file: float, output_tokens_per_file: float) -> float:
    """Estimate cost for running a model on a dataset."""
    total_input_tokens = files * input_tokens_per_file
    total_output_tokens = files * output_tokens_per_file
    
    input_cost = (total_input_tokens / 1_000_000) * model.input_cost_per_million
    output_cost = (total_output_tokens / 1_000_000) * model.output_cost_per_million
    
    return input_cost + output_cost


def estimate_time(files: int, time_per_file: float) -> float:
    """Estimate time in hours for running on a dataset."""
    return (files * time_per_file) / 3600  # Convert seconds to hours


def generate_experiment_plan():
    """Generate and display the experiment plan with cost and time estimates."""
    time_per_file, input_tokens_per_file, output_tokens_per_file = calculate_baseline_metrics()
    
    print("=== BASELINE METRICS ===")
    print(f"Time per file: {time_per_file:.1f} seconds")
    print(f"Input tokens per file: {input_tokens_per_file:.0f}")
    print(f"Output tokens per file: {output_tokens_per_file:.0f}")
    print()
    
    print("=== EXPERIMENT PLAN ===")
    print(f"{'Dataset':<15} {'Files':<6} {'Model':<15} {'Est. Cost ($)':<12} {'Est. Time (h)':<13} {'Command'}")
    print("-" * 120)
    
    total_cost = 0
    total_time_hours = 0
    total_experiments = 0
    
    for dataset in DATASETS:
        for model in MODELS:
            cost = estimate_cost(model, dataset.file_count, input_tokens_per_file, output_tokens_per_file)
            time_hours = estimate_time(dataset.file_count, time_per_file)
            
            command = f"uv run src/vericoder.py lean {dataset.path} --llm-provider {model.provider}"
            
            print(f"{dataset.name:<15} {dataset.file_count:<6} {model.name:<15} ${cost:<11.2f} {time_hours:<13.1f} {command}")
            
            total_cost += cost
            total_time_hours += time_hours
            total_experiments += 1
    
    print("-" * 120)
    print(f"{'TOTAL':<15} {sum(d.file_count for d in DATASETS):<6} {total_experiments} experiments ${total_cost:<11.2f} {total_time_hours:<13.1f}")
    print()
    
    print("=== SUMMARY ===")
    print(f"Total experiments: {total_experiments}")
    print(f"Total files to process: {sum(d.file_count for d in DATASETS):,}")
    print(f"Estimated total cost: ${total_cost:.2f}")
    print(f"Estimated total time: {total_time_hours:.1f} hours ({total_time_hours/24:.1f} days)")
    print(f"Average cost per experiment: ${total_cost/total_experiments:.2f}")
    print(f"Average time per experiment: {total_time_hours/total_experiments:.1f} hours")


def run_experiments(dry_run: bool = True, dataset_filter: str = None, model_filter: str = None):
    """Run the experiments."""
    time_per_file, input_tokens_per_file, output_tokens_per_file = calculate_baseline_metrics()
    
    print("=== RUNNING EXPERIMENTS ===")
    if dry_run:
        print("DRY RUN MODE - Commands will be printed but not executed")
    print()
    
    experiments_run = 0
    
    for dataset in DATASETS:
        if dataset_filter and dataset_filter not in dataset.name:
            continue
            
        for model in MODELS:
            if model_filter and model_filter not in model.name:
                continue
                
            cost = estimate_cost(model, dataset.file_count, input_tokens_per_file, output_tokens_per_file)
            time_hours = estimate_time(dataset.file_count, time_per_file)
            
            command = [
                "uv", "run", "src/vericoder.py", "lean", dataset.path,
                "--llm-provider", model.provider
            ]
            
            print(f"Experiment {experiments_run + 1}: {dataset.name} + {model.name}")
            print(f"  Files: {dataset.file_count}, Est. cost: ${cost:.2f}, Est. time: {time_hours:.1f}h")
            print(f"  Command: {' '.join(command)}")
            
            if not dry_run:
                try:
                    result = subprocess.run(command, check=True, cwd=Path(__file__).parent.parent.parent)
                    print(f"  ✓ Completed successfully")
                except subprocess.CalledProcessError as e:
                    print(f"  ✗ Failed with exit code {e.returncode}")
                except KeyboardInterrupt:
                    print(f"  ⚠ Interrupted by user")
                    return experiments_run
            else:
                print(f"  (dry run - not executed)")
            
            print()
            experiments_run += 1
    
    print(f"Completed {experiments_run} experiments")
    return experiments_run


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Batch experiment runner for vericoding")
    parser.add_argument("--run", action="store_true", help="Actually run experiments (default is dry run)")
    parser.add_argument("--dataset", help="Filter by dataset name (substring match)")
    parser.add_argument("--model", help="Filter by model name (substring match)")
    parser.add_argument("--plan-only", action="store_true", help="Only show the experiment plan, don't run")
    
    args = parser.parse_args()
    
    if args.plan_only:
        generate_experiment_plan()
    else:
        generate_experiment_plan()
        print()
        run_experiments(dry_run=not args.run, dataset_filter=args.dataset, model_filter=args.model)


if __name__ == "__main__":
    main()