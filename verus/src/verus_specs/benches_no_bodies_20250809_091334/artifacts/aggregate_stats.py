#!/usr/bin/env python3
"""
Script to aggregate statistics from artifacts/dafnybench/*/success.yml files
and output them to a CSV file.
"""

import csv
import yaml
from pathlib import Path
from typing import Dict, List, Any


def find_success_files(artifacts_dir: Path) -> List[Path]:
    """Find all success.yml files in the artifacts/dafnybench directory."""
    dafnybench_dir = artifacts_dir / "dafnybench"
    if not dafnybench_dir.exists():
        print(f"Directory {dafnybench_dir} does not exist")
        return []
    
    success_files = list(dafnybench_dir.glob("*/success.yml"))
    print(f"Found {len(success_files)} success.yml files")
    return success_files


def parse_success_file(file_path: Path) -> Dict[str, Any]:
    """Parse a single success.yml file and return the data with directory name."""
    try:
        with open(file_path, 'r') as f:
            data = yaml.safe_load(f)
        
        # Add the directory name as an identifier
        data['directory'] = file_path.parent.name
        return data
    except Exception as e:
        print(f"Error parsing {file_path}: {e}")
        return {
            'directory': file_path.parent.name,
            'success': False,
            'num_iterations': 0,
            'error': str(e)
        }


def aggregate_statistics(data_list: List[Dict[str, Any]]) -> Dict[str, Any]:
    """Calculate aggregate statistics from all the data."""
    total_items = len(data_list)
    successful_items = sum(1 for item in data_list if item.get('success', False))
    failed_items = total_items - successful_items
    
    # Calculate iteration statistics
    iterations = [item.get('num_iterations', 0) for item in data_list]
    successful_iterations = [item.get('num_iterations', 0) for item in data_list if item.get('success', False)]
    failed_iterations = [item.get('num_iterations', 0) for item in data_list if not item.get('success', False)]
    
    stats = {
        'total_items': total_items,
        'successful_items': successful_items,
        'failed_items': failed_items,
        'success_rate': (successful_items / total_items * 100) if total_items > 0 else 0,
        'total_iterations': sum(iterations),
        'avg_iterations': sum(iterations) / len(iterations) if iterations else 0,
        'max_iterations': max(iterations) if iterations else 0,
        'min_iterations': min(iterations) if iterations else 0,
        'avg_iterations_successful': sum(successful_iterations) / len(successful_iterations) if successful_iterations else 0,
        'avg_iterations_failed': sum(failed_iterations) / len(failed_iterations) if failed_iterations else 0,
    }
    
    return stats


def write_individual_csv(data_list: List[Dict[str, Any]], output_file: Path):
    """Write individual item data to CSV."""
    if not data_list:
        return
    
    # Get all possible keys for the CSV header
    all_keys = set()
    for item in data_list:
        all_keys.update(item.keys())
    
    # Sort keys for consistent output
    fieldnames = sorted(all_keys)
    
    with open(output_file, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(data_list)
    
    print(f"Individual results written to {output_file}")


def write_aggregate_csv(stats: Dict[str, Any], output_file: Path):
    """Write aggregate statistics to CSV."""
    with open(output_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['Statistic', 'Value'])
        
        for key, value in stats.items():
            if isinstance(value, float):
                writer.writerow([key, f"{value:.2f}"])
            else:
                writer.writerow([key, value])
    
    print(f"Aggregate statistics written to {output_file}")


def main():
    """Main function to aggregate statistics and generate CSV files."""
    artifacts_dir = Path("artifacts")
    
    # Find all success.yml files
    success_files = find_success_files(artifacts_dir)
    
    if not success_files:
        print("No success.yml files found")
        return
    
    # Parse all files
    data_list = []
    for file_path in success_files:
        data = parse_success_file(file_path)
        data_list.append(data)
    
    # Calculate aggregate statistics
    stats = aggregate_statistics(data_list)
    
    # Write individual results to CSV
    write_individual_csv(data_list, Path("dafnybench_individual_results.csv"))
    
    # Write aggregate statistics to CSV
    write_aggregate_csv(stats, Path("dafnybench_aggregate_stats.csv"))
    
    # Print summary
    print("\nSummary:")
    print(f"Total items: {stats['total_items']}")
    print(f"Successful: {stats['successful_items']} ({stats['success_rate']:.1f}%)")
    print(f"Failed: {stats['failed_items']}")
    print(f"Average iterations: {stats['avg_iterations']:.1f}")
    print(f"Average iterations (successful): {stats['avg_iterations_successful']:.1f}")
    print(f"Average iterations (failed): {stats['avg_iterations_failed']:.1f}")


if __name__ == "__main__":
    main()