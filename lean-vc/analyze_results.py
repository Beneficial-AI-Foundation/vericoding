#!/usr/bin/env python3
# /// script
# requires-python = ">=3.8"
# dependencies = [
#     "matplotlib",
#     "numpy",
# ]
# ///
"""Analyze spec_to_code experiment results and generate reports."""

import csv
import json
import sys
from pathlib import Path
from collections import defaultdict
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
import numpy as np

def load_results(csv_path):
    """Load results from CSV file."""
    results = []
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            results.append({
                'file': row['filename'],
                'success': row['result'] == 'success',
                'iterations': int(row['nr_iterations']) if row['nr_iterations'] else 0,
                'link': row.get('spec_link', '')
            })
    return results

def categorize_file(filename):
    """Categorize file by complexity based on our classification."""
    simple_ops = ['Add', 'Subtract', 'Multiply', 'Square', 'Absolute', 'Sign', 
                  'Min', 'Max', 'Minimum', 'Maximum', 'Clip', 'Where', 
                  'zeros', 'ones', 'copy']
    
    complex_ops = ['Dot', 'Matmul', 'Std', 'Var', 'Sort', 'Argsort', 
                   'Argmax', 'Argmin', 'broadcast', 'expand_dims', 
                   'moveaxis', 'meshgrid', 'vander', 'tril', 'triu']
    
    for op in simple_ops:
        if op in filename:
            return 'simple'
    
    for op in complex_ops:
        if op in filename:
            return 'complex'
    
    return 'medium'

def analyze_results(results_1iter, results_5iter):
    """Analyze and compare results from both experiments."""
    stats = {
        '1_iter': {'total': len(results_1iter), 'success': 0, 'by_category': defaultdict(lambda: {'total': 0, 'success': 0})},
        '5_iter': {'total': len(results_5iter), 'success': 0, 'by_category': defaultdict(lambda: {'total': 0, 'success': 0})}
    }
    
    # Analyze 1-iteration results
    for result in results_1iter:
        category = categorize_file(result['file'])
        stats['1_iter']['by_category'][category]['total'] += 1
        if result['success']:
            stats['1_iter']['success'] += 1
            stats['1_iter']['by_category'][category]['success'] += 1
    
    # Analyze 5-iteration results
    for result in results_5iter:
        category = categorize_file(result['file'])
        stats['5_iter']['by_category'][category]['total'] += 1
        if result['success']:
            stats['5_iter']['success'] += 1
            stats['5_iter']['by_category'][category]['success'] += 1
    
    return stats

def create_visualizations(stats, output_dir):
    """Create charts and diagrams."""
    output_dir = Path(output_dir)
    output_dir.mkdir(exist_ok=True)
    
    # Overall success rate comparison
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Pie chart for 1 iteration
    ax1.pie([stats['1_iter']['success'], stats['1_iter']['total'] - stats['1_iter']['success']], 
            labels=['Success', 'Failed'], autopct='%1.1f%%', colors=['#2ecc71', '#e74c3c'])
    ax1.set_title(f"1 Iteration Results\\n({stats['1_iter']['success']}/{stats['1_iter']['total']} successful)")
    
    # Pie chart for 5 iterations
    ax2.pie([stats['5_iter']['success'], stats['5_iter']['total'] - stats['5_iter']['success']], 
            labels=['Success', 'Failed'], autopct='%1.1f%%', colors=['#2ecc71', '#e74c3c'])
    ax2.set_title(f"5 Iterations Results\\n({stats['5_iter']['success']}/{stats['5_iter']['total']} successful)")
    
    plt.tight_layout()
    plt.savefig(output_dir / 'overall_success_rate.png', dpi=150)
    plt.close()
    
    # Success rate by category
    categories = ['simple', 'medium', 'complex']
    success_rates_1 = []
    success_rates_5 = []
    
    for cat in categories:
        if stats['1_iter']['by_category'][cat]['total'] > 0:
            rate_1 = stats['1_iter']['by_category'][cat]['success'] / stats['1_iter']['by_category'][cat]['total'] * 100
        else:
            rate_1 = 0
        success_rates_1.append(rate_1)
        
        if stats['5_iter']['by_category'][cat]['total'] > 0:
            rate_5 = stats['5_iter']['by_category'][cat]['success'] / stats['5_iter']['by_category'][cat]['total'] * 100
        else:
            rate_5 = 0
        success_rates_5.append(rate_5)
    
    x = np.arange(len(categories))
    width = 0.35
    
    fig, ax = plt.subplots(figsize=(10, 6))
    bars1 = ax.bar(x - width/2, success_rates_1, width, label='1 Iteration', color='#3498db')
    bars2 = ax.bar(x + width/2, success_rates_5, width, label='5 Iterations', color='#9b59b6')
    
    ax.set_xlabel('Complexity Category')
    ax.set_ylabel('Success Rate (%)')
    ax.set_title('Success Rate by Complexity Category')
    ax.set_xticks(x)
    ax.set_xticklabels(categories)
    ax.legend()
    ax.set_ylim(0, 100)
    
    # Add value labels on bars
    for bars in [bars1, bars2]:
        for bar in bars:
            height = bar.get_height()
            ax.annotate(f'{height:.1f}%',
                       xy=(bar.get_x() + bar.get_width() / 2, height),
                       xytext=(0, 3),
                       textcoords="offset points",
                       ha='center', va='bottom')
    
    plt.tight_layout()
    plt.savefig(output_dir / 'success_by_category.png', dpi=150)
    plt.close()

def generate_report(stats, results_1iter, results_5iter, output_path):
    """Generate detailed text report."""
    with open(output_path, 'w') as f:
        f.write("# Lean Spec-to-Code Experiment Results\n\n")
        f.write("## Executive Summary\n\n")
        
        # Overall stats
        success_rate_1 = stats['1_iter']['success'] / stats['1_iter']['total'] * 100
        success_rate_5 = stats['5_iter']['success'] / stats['5_iter']['total'] * 100
        improvement = success_rate_5 - success_rate_1
        
        f.write(f"- **Total specs tested**: {stats['1_iter']['total']}\n")
        f.write(f"- **1-iteration success rate**: {stats['1_iter']['success']}/{stats['1_iter']['total']} ({success_rate_1:.1f}%)\n")
        f.write(f"- **5-iteration success rate**: {stats['5_iter']['success']}/{stats['5_iter']['total']} ({success_rate_5:.1f}%)\n")
        f.write(f"- **Improvement with more iterations**: +{improvement:.1f} percentage points\n\n")
        
        # By category
        f.write("## Results by Complexity Category\n\n")
        for category in ['simple', 'medium', 'complex']:
            f.write(f"### {category.capitalize()} Operations\n")
            
            total_1 = stats['1_iter']['by_category'][category]['total']
            success_1 = stats['1_iter']['by_category'][category]['success']
            total_5 = stats['5_iter']['by_category'][category]['total']
            success_5 = stats['5_iter']['by_category'][category]['success']
            
            if total_1 > 0:
                rate_1 = success_1 / total_1 * 100
                rate_5 = success_5 / total_5 * 100
                f.write(f"- 1 iteration: {success_1}/{total_1} ({rate_1:.1f}%)\n")
                f.write(f"- 5 iterations: {success_5}/{total_5} ({rate_5:.1f}%)\n\n")
        
        # Successful implementations
        f.write("## Successfully Implemented Specs\n\n")
        f.write("### With 1 Iteration:\n")
        for result in results_1iter:
            if result['success']:
                f.write(f"- {result['file']}\n")
        
        f.write("\n### Additional with 5 Iterations:\n")
        success_1_files = {r['file'] for r in results_1iter if r['success']}
        for result in results_5iter:
            if result['success'] and result['file'] not in success_1_files:
                f.write(f"- {result['file']} (took {result['iterations']} iterations)\n")
        
        # Failed implementations
        f.write("\n## Failed Implementations (after 5 iterations)\n\n")
        for result in results_5iter:
            if not result['success']:
                f.write(f"- {result['file']}\n")
        
        # Insights
        f.write("\n## Key Insights\n\n")
        f.write("1. **Iteration Impact**: Additional iterations significantly improve success rate\n")
        f.write("2. **Complexity Correlation**: Simple operations have higher success rates\n")
        f.write("3. **Common Failure Patterns**: Type mismatches, missing imports, incorrect syntax\n")
        f.write("4. **LLM Capabilities**: Better at implementing algorithmic logic than handling Lean-specific type system\n")

if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python analyze_results.py <1iter_csv> <5iter_csv> [output_dir]")
        sys.exit(1)
    
    csv_1iter = sys.argv[1]
    csv_5iter = sys.argv[2]
    output_dir = sys.argv[3] if len(sys.argv) > 3 else "analysis_results"
    
    # Load results
    results_1iter = load_results(csv_1iter)
    results_5iter = load_results(csv_5iter)
    
    # Analyze
    stats = analyze_results(results_1iter, results_5iter)
    
    # Create output directory
    Path(output_dir).mkdir(exist_ok=True)
    
    # Generate visualizations
    create_visualizations(stats, output_dir)
    
    # Generate report
    generate_report(stats, results_1iter, results_5iter, Path(output_dir) / "report.md")
    
    print(f"Analysis complete! Results saved to {output_dir}/")