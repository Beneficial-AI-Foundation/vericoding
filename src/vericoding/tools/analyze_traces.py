#!/usr/bin/env python3
"""
Analyze experiment traces to understand Claude's reasoning process.
"""

import json
import gzip
from pathlib import Path
from typing import Dict, List, Optional, Union
import argparse
from collections import defaultdict

from vericoding.tools.trace_logger import TraceLogger


def analyze_trace_directory(trace_dir: Path) -> Dict:
    """
    Analyze all traces in a directory.
    
    Returns comprehensive statistics about the traces.
    """
    trace_logger = TraceLogger(trace_dir=trace_dir)
    
    stats = {
        "total_traces": 0,
        "successful_traces": 0,
        "failed_traces": 0,
        "mcp_traces": 0,
        "non_mcp_traces": 0,
        "average_turns": 0,
        "average_iterations": 0,
        "tool_usage": defaultdict(int),
        "common_error_patterns": defaultdict(int),
        "languages": defaultdict(int),
        "traces": []
    }
    
    # Find all trace files
    trace_files = list(trace_dir.glob("trace_*.json*"))
    
    for trace_file in trace_files:
        try:
            trace = trace_logger.load_trace(trace_file)
            summary = trace_logger.create_trace_summary(trace)
            
            stats["total_traces"] += 1
            stats["languages"][trace.language] += 1
            
            if trace.use_mcp:
                stats["mcp_traces"] += 1
            else:
                stats["non_mcp_traces"] += 1
            
            if summary["final_success"]:
                stats["successful_traces"] += 1
            else:
                stats["failed_traces"] += 1
            
            # Track tool usage
            for tool in summary["unique_tools"]:
                stats["tool_usage"][tool] += 1
            
            # Add trace summary
            stats["traces"].append({
                "file": trace_file.name,
                "summary": summary
            })
            
        except Exception as e:
            print(f"Error loading trace {trace_file}: {e}")
    
    # Calculate averages
    if stats["total_traces"] > 0:
        total_turns = sum(t["summary"]["total_turns"] for t in stats["traces"])
        total_iterations = sum(t["summary"]["verification_attempts"] for t in stats["traces"])
        
        stats["average_turns"] = total_turns / stats["total_traces"]
        stats["average_iterations"] = total_iterations / stats["total_traces"]
    
    return stats


def find_interesting_patterns(trace_dir: Path) -> List[Dict]:
    """
    Find interesting patterns in traces that might indicate good or bad strategies.
    """
    trace_logger = TraceLogger(trace_dir=trace_dir)
    patterns = []
    
    trace_files = list(trace_dir.glob("trace_*.json*"))
    
    for trace_file in trace_files:
        try:
            trace = trace_logger.load_trace(trace_file)
            
            # Pattern 1: Traces that succeeded quickly
            if trace.verification_results and trace.verification_results[0]["success"]:
                patterns.append({
                    "type": "quick_success",
                    "file": trace.file_name,
                    "trace_file": trace_file.name,
                    "description": "Succeeded on first attempt"
                })
            
            # Pattern 2: Traces that used many MCP tools
            tool_count = sum(len(turn.tools_used) for turn in trace.turns)
            if tool_count > 10:
                patterns.append({
                    "type": "heavy_tool_usage",
                    "file": trace.file_name,
                    "trace_file": trace_file.name,
                    "tool_count": tool_count,
                    "description": f"Used {tool_count} tool calls"
                })
            
            # Pattern 3: Traces with repeated errors
            if len(trace.verification_results) >= 3:
                errors = [r["output"] for r in trace.verification_results if not r["success"]]
                if len(set(errors)) < len(errors) * 0.5:
                    patterns.append({
                        "type": "repeated_errors",
                        "file": trace.file_name,
                        "trace_file": trace_file.name,
                        "description": "Similar errors across multiple attempts"
                    })
            
        except Exception as e:
            print(f"Error analyzing trace {trace_file}: {e}")
    
    return patterns


def extract_successful_strategies(trace_dir: Path) -> List[Dict]:
    """
    Extract successful problem-solving strategies from traces.
    """
    trace_logger = TraceLogger(trace_dir=trace_dir)
    strategies = []
    
    trace_files = list(trace_dir.glob("trace_*.json*"))
    
    for trace_file in trace_files:
        try:
            trace = trace_logger.load_trace(trace_file)
            
            # Only analyze successful traces
            if not trace.verification_results or not trace.verification_results[-1]["success"]:
                continue
            
            # Extract strategy based on tool usage pattern
            tools_sequence = []
            for turn in trace.turns:
                tools_sequence.extend([t["name"] for t in turn.tools_used])
            
            strategy = {
                "file": trace.file_name,
                "trace_file": trace_file.name,
                "total_turns": len(trace.turns),
                "tools_used": tools_sequence,
                "iterations_needed": len(trace.verification_results),
                "key_tools": list(set(tools_sequence))
            }
            
            # Identify key moments
            if "lean_leansearch" in tools_sequence or "lean_loogle" in tools_sequence:
                strategy["used_search"] = True
            
            if "lean_goal" in tools_sequence:
                strategy["examined_proof_state"] = True
            
            strategies.append(strategy)
            
        except Exception as e:
            print(f"Error extracting strategy from {trace_file}: {e}")
    
    return strategies


def main():
    parser = argparse.ArgumentParser(description="Analyze experiment traces")
    parser.add_argument("trace_dir", type=Path, help="Directory containing trace files")
    parser.add_argument("--report", type=str, help="Save analysis report to file")
    parser.add_argument("--patterns", action="store_true", help="Find interesting patterns")
    parser.add_argument("--strategies", action="store_true", help="Extract successful strategies")
    
    args = parser.parse_args()
    
    if not args.trace_dir.exists():
        print(f"Error: Directory {args.trace_dir} does not exist")
        return
    
    # Basic analysis
    print("Analyzing traces...")
    stats = analyze_trace_directory(args.trace_dir)
    
    print("\n=== Trace Analysis Summary ===")
    print(f"Total traces: {stats['total_traces']}")
    print(f"Successful: {stats['successful_traces']} ({stats['successful_traces']/stats['total_traces']*100:.1f}%)")
    print(f"Failed: {stats['failed_traces']}")
    print(f"MCP-enabled: {stats['mcp_traces']}")
    print(f"Average turns: {stats['average_turns']:.1f}")
    print(f"Average iterations: {stats['average_iterations']:.1f}")
    
    print("\n=== Tool Usage ===")
    for tool, count in sorted(stats['tool_usage'].items(), key=lambda x: x[1], reverse=True):
        print(f"{tool}: {count}")
    
    # Find patterns
    if args.patterns:
        print("\n=== Interesting Patterns ===")
        patterns = find_interesting_patterns(args.trace_dir)
        for pattern in patterns:
            print(f"- {pattern['type']}: {pattern['description']} ({pattern['file']})")
    
    # Extract strategies
    if args.strategies:
        print("\n=== Successful Strategies ===")
        strategies = extract_successful_strategies(args.trace_dir)
        for strategy in strategies[:5]:  # Show top 5
            print(f"\nFile: {strategy['file']}")
            print(f"  Turns: {strategy['total_turns']}, Iterations: {strategy['iterations_needed']}")
            print(f"  Key tools: {', '.join(strategy['key_tools'][:5])}")
    
    # Save report if requested
    if args.report:
        report = {
            "summary": stats,
            "patterns": find_interesting_patterns(args.trace_dir) if args.patterns else [],
            "strategies": extract_successful_strategies(args.trace_dir) if args.strategies else []
        }
        
        with open(args.report, "w") as f:
            json.dump(report, f, indent=2)
        
        print(f"\nReport saved to {args.report}")


if __name__ == "__main__":
    main()