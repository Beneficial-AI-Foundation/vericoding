#!/usr/bin/env python3
# /// script
# requires-python = ">=3.8"
# dependencies = [
#     "matplotlib",
#     "numpy",
# ]
# ///

"""Create visualizations for spec_to_code experiment results."""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path

def create_success_rate_diagram(output_path):
    """Create a visual diagram showing success rates."""
    fig, ax = plt.subplots(figsize=(12, 8))
    
    # Define the specs grid (10x5 = 50 specs)
    rows, cols = 10, 5
    
    # Create color mapping
    # 0 = failed both, 1 = success 1-iter only, 2 = success 5-iter only, 3 = success both
    colors = {
        0: '#e74c3c',  # Red - failed
        1: '#3498db',  # Blue - 1-iter success
        2: '#9b59b6',  # Purple - 5-iter success  
        3: '#2ecc71',  # Green - both success
    }
    
    # Placeholder data (will be replaced with actual results)
    # For now, simulate some results
    np.random.seed(42)
    results = np.random.choice([0, 0, 0, 1, 2, 3], size=(rows, cols), p=[0.6, 0.1, 0.2, 0.05, 0.04, 0.01])
    
    # Create the grid
    for i in range(rows):
        for j in range(cols):
            spec_num = i * cols + j
            color = colors[results[i, j]]
            rect = plt.Rectangle((j, rows-i-1), 1, 1, facecolor=color, edgecolor='black', linewidth=1)
            ax.add_patch(rect)
            
            # Add spec number
            ax.text(j + 0.5, rows-i-0.5, str(spec_num + 1), 
                   ha='center', va='center', fontsize=8, weight='bold')
    
    # Set up the plot
    ax.set_xlim(0, cols)
    ax.set_ylim(0, rows)
    ax.set_aspect('equal')
    ax.axis('off')
    
    # Add title and legend
    plt.title('Lean Spec-to-Code Success Map (50 Specs)', fontsize=16, weight='bold', pad=20)
    
    # Create legend
    legend_elements = [
        mpatches.Patch(color=colors[0], label='Failed (both)'),
        mpatches.Patch(color=colors[1], label='Success (1 iter only)'),
        mpatches.Patch(color=colors[2], label='Success (5 iter only)'),
        mpatches.Patch(color=colors[3], label='Success (both)')
    ]
    ax.legend(handles=legend_elements, loc='center', bbox_to_anchor=(0.5, -0.1), ncol=4, fontsize=10)
    
    # Add category labels
    ax.text(-1, 8.5, 'Simple\n(1-15)', ha='right', va='center', fontsize=10, style='italic')
    ax.text(-1, 4, 'Medium\n(16-35)', ha='right', va='center', fontsize=10, style='italic')
    ax.text(-1, 0.5, 'Complex\n(36-50)', ha='right', va='center', fontsize=10, style='italic')
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()

def create_iteration_impact_chart(output_path):
    """Create a chart showing the impact of iterations."""
    # Placeholder data
    categories = ['Overall', 'Simple', 'Medium', 'Complex']
    success_1iter = [8, 20, 5, 0]  # Placeholder percentages
    success_5iter = [24, 40, 25, 6.7]  # Placeholder percentages
    
    x = np.arange(len(categories))
    width = 0.35
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    bars1 = ax.bar(x - width/2, success_1iter, width, label='1 Iteration', color='#3498db', alpha=0.8)
    bars2 = ax.bar(x + width/2, success_5iter, width, label='5 Iterations', color='#9b59b6', alpha=0.8)
    
    # Add improvement arrows
    for i in range(len(categories)):
        if success_5iter[i] > success_1iter[i]:
            ax.annotate('', xy=(x[i] + width/2, success_5iter[i]), 
                       xytext=(x[i] - width/2, success_1iter[i]),
                       arrowprops=dict(arrowstyle='->', color='green', lw=2))
            
            # Add improvement percentage
            improvement = success_5iter[i] - success_1iter[i]
            ax.text(x[i], (success_1iter[i] + success_5iter[i])/2, 
                   f'+{improvement:.0f}%', ha='center', va='center',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7))
    
    ax.set_xlabel('Complexity Category', fontsize=12)
    ax.set_ylabel('Success Rate (%)', fontsize=12)
    ax.set_title('Impact of Iterations on Success Rate', fontsize=14, weight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(categories)
    ax.legend()
    ax.set_ylim(0, 50)
    ax.grid(True, axis='y', alpha=0.3)
    
    # Add value labels on bars
    for bars in [bars1, bars2]:
        for bar in bars:
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height + 1,
                   f'{height:.0f}%', ha='center', va='bottom', fontsize=9)
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()

def create_failure_analysis_chart(output_path):
    """Create a chart analyzing failure modes."""
    labels = ['Type System\nErrors', 'Syntax\nErrors', 'Proof\nFailures', 'Import/Library\nIssues', 'Other']
    sizes = [35, 25, 20, 15, 5]  # Placeholder percentages
    colors = ['#e74c3c', '#f39c12', '#9b59b6', '#3498db', '#95a5a6']
    explode = (0.1, 0, 0, 0, 0)  # explode 1st slice
    
    fig, ax = plt.subplots(figsize=(8, 8))
    ax.pie(sizes, explode=explode, labels=labels, colors=colors, autopct='%1.1f%%',
           shadow=True, startangle=90)
    ax.axis('equal')
    
    plt.title('Distribution of Failure Modes', fontsize=14, weight='bold', pad=20)
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()

if __name__ == "__main__":
    output_dir = Path("experiment_visualizations")
    output_dir.mkdir(exist_ok=True)
    
    print("Creating visualizations...")
    create_success_rate_diagram(output_dir / "success_map.png")
    create_iteration_impact_chart(output_dir / "iteration_impact.png")
    create_failure_analysis_chart(output_dir / "failure_modes.png")
    print(f"Visualizations saved to {output_dir}/")