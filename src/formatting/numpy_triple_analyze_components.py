#!/usr/bin/env python3
"""
Script to analyze parsing_results.json and summarize different component orders.
"""

import json
from collections import Counter, defaultdict


def analyze_parsing_results(json_file_path: str):
    """Analyze the parsing results and summarize component orders."""

    # Load the JSON data
    with open(json_file_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    print("=" * 60)

    # Count status types
    status_counts = Counter()
    component_order_counts = Counter()
    component_order_examples = defaultdict(list)

    for filename, file_data in data.items():
        status = file_data["status"]
        status_counts[status] += 1

        if "results" in file_data and file_data["results"]:
            # Extract component order
            component_order = tuple(
                result["type"] + ("1" if "sorry" in result["string"] else "0")
                for result in file_data["results"]
            )
            component_order_counts[component_order] += 1
            component_order_examples[component_order].append(filename)

    # Print status summary
    print("STATUS SUMMARY:")
    print("-" * 30)
    print(f"Total files analyzed: {len(data)}")
    for status, count in status_counts.most_common():
        print(f"{status}: {count} files")

    print("\n" + "=" * 60)
    print("COMPONENT ORDER ANALYSIS:")
    print("-" * 40)

    if not component_order_counts:
        print("No component orders found (all files had parsing errors)")
        return

    # Print component order summary
    print(f"Total unique component orders: {len(component_order_counts)}")
    print()

    for order, count in component_order_counts.most_common():
        print(f"Order: {list(order)}")
        print(f"Count: {count} files")
        print(f"Percentage: {count / len(data) * 100:.1f}%")

        # Show first few examples
        examples = component_order_examples[order][:3]
        if examples:
            print(f"Examples: {', '.join(examples)}")

        print("-" * 40)

    # Detailed analysis of most common orders
    print("\n" + "=" * 60)
    print("DETAILED ANALYSIS OF MOST COMMON ORDERS:")
    print("-" * 50)

    for order, count in component_order_counts.most_common(5):
        print(f"\nOrder: {list(order)}")
        print(f"Count: {count} files")
        print("All files with this order:")
        for filename in component_order_examples[order]:
            print(f"  - {filename}")

    # Analyze common patterns
    print("\n" + "=" * 60)
    print("COMMON PATTERNS ANALYSIS:")
    print("-" * 30)

    # Count files that start with desc
    desc_start_count = sum(
        count
        for order, count in component_order_counts.items()
        if order and order[0] == "desc"
    )
    print(f"Files starting with 'desc': {desc_start_count}")

    # Count files that start with imports
    imports_start_count = sum(
        count
        for order, count in component_order_counts.items()
        if order and order[0] == "imports"
    )
    print(f"Files starting with 'imports': {imports_start_count}")

    # Count files with 'constr' component
    constr_count = sum(
        count for order, count in component_order_counts.items() if "constr" in order
    )
    print(f"Files with 'constr' component: {constr_count}")

    # Count files with 'comment' component
    comment_count = sum(
        count for order, count in component_order_counts.items() if "comment" in order
    )
    print(f"Files with 'comment' component: {comment_count}")

    # Count files with 'empty' component
    empty_count = sum(
        count for order, count in component_order_counts.items() if "empty" in order
    )
    print(f"Files with 'empty' component: {empty_count}")


if __name__ == "__main__":
    json_file_path = "benchmarks/lean/parsing_results.json"
    analyze_parsing_results(json_file_path)
