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


def calculate_file_limit_for_budget(cost_limit: float) -> int:
    """Calculate the maximum files per experiment to stay within budget."""
    time_per_file, input_tokens_per_file, output_tokens_per_file = calculate_baseline_metrics()
    
    # Calculate total cost if we run 1 file per experiment
    total_experiments = len(DATASETS) * len(MODELS)
    cost_per_file_per_experiment = []
    
    for dataset in DATASETS:
        for model in MODELS:
            cost_1_file = estimate_cost(model, 1, input_tokens_per_file, output_tokens_per_file)
            cost_per_file_per_experiment.append(cost_1_file)
    
    # Sum cost for 1 file across all experiments
    total_cost_1_file = sum(cost_per_file_per_experiment)
    
    # Calculate max files per experiment to stay under budget
    if total_cost_1_file > cost_limit:
        return 0  # Budget too low even for 1 file per experiment
    
    max_files = int(cost_limit / total_cost_1_file)
    return max_files


def generate_experiment_plan(file_limit: int = None):
    """Generate and display the experiment plan with cost and time estimates."""
    time_per_file, input_tokens_per_file, output_tokens_per_file = calculate_baseline_metrics()
    
    print("=== BASELINE METRICS ===")
    print(f"Time per file: {time_per_file:.1f} seconds")
    print(f"Input tokens per file: {input_tokens_per_file:.0f}")
    print(f"Output tokens per file: {output_tokens_per_file:.0f}")
    print()
    
    if file_limit:
        print(f"=== FILE LIMIT: {file_limit} files per experiment ===")
        print()
    
    print("=== EXPERIMENT PLAN ===")
    print(f"{'Dataset':<15} {'Files':<6} {'Model':<15} {'Est. Cost ($)':<12} {'Est. Time (h)':<13} {'Command'}")
    print("-" * 120)
    
    total_cost = 0
    total_time_hours = 0
    total_experiments = 0
    
    for dataset in DATASETS:
        for model in MODELS:
            # Apply file limit if specified
            actual_files = min(dataset.file_count, file_limit) if file_limit else dataset.file_count
            
            cost = estimate_cost(model, actual_files, input_tokens_per_file, output_tokens_per_file)
            time_hours = estimate_time(actual_files, time_per_file)
            
            command = f"uv run src/vericoder.py lean {dataset.path} --llm-provider {model.provider}"
            
            # Add assume-unformatted-lean for "poor" datasets (unformatted Lean files)
            if "poor" in dataset.path:
                command += " --assume-unformatted-lean"
            
            # Add limit if specified
            if file_limit and file_limit < dataset.file_count:
                command += f" --limit {file_limit}"
            
            print(f"{dataset.name:<15} {actual_files:<6} {model.name:<15} ${cost:<11.2f} {time_hours:<13.1f} {command}")
            
            total_cost += cost
            total_time_hours += time_hours
            total_experiments += 1
    
    print("-" * 120)
    
    # Calculate actual total files processed with limit
    total_files_actual = 0
    for dataset in DATASETS:
        actual_files = min(dataset.file_count, file_limit) if file_limit else dataset.file_count
        total_files_actual += actual_files
    
    print(f"{'TOTAL':<15} {total_files_actual:<6} {total_experiments} experiments ${total_cost:<11.2f} {total_time_hours:<13.1f}")
    print()
    
    print("=== SUMMARY ===")
    print(f"Total experiments: {total_experiments}")
    print(f"Total files to process: {total_files_actual:,}")
    if file_limit:
        print(f"Original total files: {sum(d.file_count for d in DATASETS):,} (limited by budget)")
    print(f"Estimated total cost: ${total_cost:.2f}")
    print(f"Estimated total time: {total_time_hours:.1f} hours ({total_time_hours/24:.1f} days)")
    print(f"Average cost per experiment: ${total_cost/total_experiments:.2f}")
    print(f"Average time per experiment: {total_time_hours/total_experiments:.1f} hours")


def run_specific_experiments(file_limit: int = None, experiment_numbers: list = None):
    """Run only the specified experiments."""
    time_per_file, input_tokens_per_file, output_tokens_per_file = calculate_baseline_metrics()
    
    # Create experiment matrix
    experiments = []
    experiment_id = 0
    for dataset in DATASETS:
        for model in MODELS:
            experiments.append((experiment_id, dataset, model))
            experiment_id += 1
    
    # Filter experiments based on provided numbers
    selected_experiments = []
    for exp_num in experiment_numbers:
        if 0 <= exp_num < len(experiments):
            selected_experiments.append(experiments[exp_num])
        else:
            print(f"Warning: Experiment {exp_num} doesn't exist (max: {len(experiments)-1})")
    
    if not selected_experiments:
        print("No valid experiments to run")
        return
    
    print(f"=== RUNNING {len(selected_experiments)} SELECTED EXPERIMENTS ===")
    
    for exp_id, dataset, model in selected_experiments:
        # Apply file limit if specified
        actual_files = min(dataset.file_count, file_limit) if file_limit else dataset.file_count
        
        command = f"uv run src/vericoder.py lean {dataset.path} --llm-provider {model.provider}"
        
        # Add assume-unformatted-lean for "poor" datasets (unformatted Lean files)
        if "poor" in dataset.path:
            command += " --assume-unformatted-lean"
        
        # Add limit if specified
        if file_limit and file_limit < dataset.file_count:
            command += f" --limit {file_limit}"
        
        cost = estimate_cost(model, actual_files, input_tokens_per_file, output_tokens_per_file)
        time_hours = estimate_time(actual_files, time_per_file)
        
        print(f"Experiment {exp_id}: {dataset.name} + {model.name}")
        print(f"  Files: {actual_files}, Est. cost: ${cost:.2f}, Est. time: {time_hours:.1f}h")
        print(f"  Command: {command}")
        print(f"  Executing...")
        
        try:
            result = subprocess.run(command.split(), check=True, cwd=Path(__file__).parent.parent.parent)
            print(f"  ✓ Completed successfully")
        except subprocess.CalledProcessError as e:
            print(f"  ✗ Failed with exit code {e.returncode}")
        except KeyboardInterrupt:
            print(f"  ⚠ Interrupted by user")
            return
        
        print()


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Batch experiment runner for vericoding")
    parser.add_argument("--cost-limit", type=float, help="Maximum total cost in USD (calculates file limit per experiment)")
    parser.add_argument("--run", help="Comma-separated list of experiment numbers to run (0-based index, e.g., '0,5,10')")
    
    args = parser.parse_args()
    
    file_limit = None
    if args.cost_limit:
        file_limit = calculate_file_limit_for_budget(args.cost_limit)
        if file_limit == 0:
            print(f"Error: Budget of ${args.cost_limit} is too low for even 1 file per experiment")
            return
        print(f"Budget: ${args.cost_limit} -> File limit: {file_limit} files per experiment")
        print()
    
    # Parse run parameter if provided
    run_experiments_list = None
    if args.run:
        try:
            run_experiments_list = [int(x.strip()) for x in args.run.split(',')]
            print(f"Running specific experiments: {run_experiments_list}")
            print()
        except ValueError:
            print("Error: --run parameter must be comma-separated integers (e.g., '0,5,10')")
            return
    
    if run_experiments_list:
        run_specific_experiments(file_limit, run_experiments_list)
    else:
        generate_experiment_plan(file_limit)


if __name__ == "__main__":
    main()
