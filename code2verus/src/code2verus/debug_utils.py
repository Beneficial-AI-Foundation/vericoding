"""Debug utilities for analyzing translation debug contexts

This module provides utilities for analyzing and reporting on debug contexts
from translation sessions, making it easier to understand what happened
during the translation process.
"""

import json
from pathlib import Path
from typing import Dict, List, Any
from datetime import datetime

from code2verus.models import TranslationDebugContext, VerificationError


def save_debug_context(
    debug_context: TranslationDebugContext, output_dir: Path = Path("debug_sessions")
) -> Path:
    """Save a debug context to a JSON file for later analysis

    Args:
        debug_context: The debug context to save
        output_dir: Directory to save the file in

    Returns:
        Path to the saved file
    """
    output_dir.mkdir(exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Create a more intuitive filename with meaningful information
    # Format: debug_session_{source_lang}_to_{target_lang}_{status}_{timestamp}_{short_id}.json
    final_status = debug_context.get_final_status()
    short_id = debug_context.session_id[:8]  # First 8 chars of UUID for uniqueness

    # Clean language names for filename
    source_lang = debug_context.source_language.replace("-", "_").lower()
    target_lang = debug_context.target_language.replace("-", "_").lower()

    # Add iteration info if available
    iter_info = (
        f"_iter{debug_context.current_iteration}"
        if debug_context.current_iteration > 0
        else ""
    )

    filename = f"debug_session_{source_lang}_to_{target_lang}_{final_status}{iter_info}_{timestamp}_{short_id}.json"
    filepath = output_dir / filename

    with open(filepath, "w") as f:
        json.dump(debug_context.model_dump(), f, indent=2, default=str)

    return filepath


def load_debug_context(filepath: Path) -> TranslationDebugContext:
    """Load a debug context from a JSON file

    Args:
        filepath: Path to the JSON file

    Returns:
        Loaded debug context
    """
    with open(filepath, "r") as f:
        data = json.load(f)

    return TranslationDebugContext.model_validate(data)


def analyze_debug_context(debug_context: TranslationDebugContext) -> Dict[str, Any]:
    """Analyze a debug context and generate insights

    Args:
        debug_context: The debug context to analyze

    Returns:
        Dictionary containing analysis results
    """
    analysis = {
        "session_summary": debug_context.to_summary_dict(),
        "iteration_breakdown": [],
        "error_patterns": analyze_error_patterns(debug_context.verification_errors),
        "conversation_analysis": analyze_conversations(
            debug_context.conversation_exchanges
        ),
        "performance_metrics": calculate_performance_metrics(debug_context),
    }

    # Analyze each iteration
    for i in range(debug_context.current_iteration):
        iteration_num = i + 1
        iteration_analysis = {
            "iteration": iteration_num,
            "had_errors": any(
                err.iteration == iteration_num
                for err in debug_context.verification_errors
            ),
            "error_types": [
                err.error_type
                for err in debug_context.verification_errors
                if err.iteration == iteration_num
            ],
            "attempt_result": next(
                (
                    att
                    for att in debug_context.previous_attempts
                    if att.iteration == iteration_num
                ),
                None,
            ),
        }
        analysis["iteration_breakdown"].append(iteration_analysis)

    return analysis


def analyze_error_patterns(errors: List[VerificationError]) -> Dict[str, Any]:
    """Analyze patterns in verification errors

    Args:
        errors: List of verification errors

    Returns:
        Dictionary containing error pattern analysis
    """
    if not errors:
        return {"total_errors": 0, "error_types": {}, "common_errors": []}

    error_types = {}
    error_messages = []

    for error in errors:
        error_types[error.error_type] = error_types.get(error.error_type, 0) + 1
        error_messages.append(error.error)

    # Find common error patterns (simplified)
    common_errors = []
    for msg in error_messages:
        if len(msg) > 50:  # Only consider substantial error messages
            common_errors.append(msg[:100] + "..." if len(msg) > 100 else msg)

    return {
        "total_errors": len(errors),
        "error_types": error_types,
        "common_errors": list(set(common_errors))[:5],  # Top 5 unique error patterns
        "error_progression": [
            {"iteration": err.iteration, "type": err.error_type} for err in errors
        ],
    }


def analyze_conversations(exchanges: List) -> Dict[str, Any]:
    """Analyze conversation exchanges for patterns

    Args:
        exchanges: List of conversation exchanges

    Returns:
        Dictionary containing conversation analysis
    """
    if not exchanges:
        return {"total_exchanges": 0}

    total_prompt_chars = sum(exc.prompt_length for exc in exchanges)
    total_response_chars = sum(exc.response_length for exc in exchanges)

    return {
        "total_exchanges": len(exchanges),
        "avg_prompt_length": total_prompt_chars / len(exchanges),
        "avg_response_length": total_response_chars / len(exchanges),
        "total_prompt_chars": total_prompt_chars,
        "total_response_chars": total_response_chars,
        "message_history_growth": [exc.message_history_length for exc in exchanges],
    }


def calculate_performance_metrics(
    debug_context: TranslationDebugContext,
) -> Dict[str, Any]:
    """Calculate performance metrics from debug context

    Args:
        debug_context: The debug context to analyze

    Returns:
        Dictionary containing performance metrics
    """
    duration = (datetime.now() - debug_context.start_time).total_seconds()

    metrics = {
        "total_duration_seconds": duration,
        "iterations_per_minute": (debug_context.current_iteration / duration) * 60
        if duration > 0
        else 0,
        "success_rate": len(
            [att for att in debug_context.previous_attempts if att.verification_success]
        )
        / len(debug_context.previous_attempts)
        if debug_context.previous_attempts
        else 0,
        "avg_iteration_time": duration / debug_context.current_iteration
        if debug_context.current_iteration > 0
        else 0,
    }

    return metrics


def generate_debug_report(debug_context: TranslationDebugContext) -> str:
    """Generate a human-readable debug report

    Args:
        debug_context: The debug context to report on

    Returns:
        Formatted debug report string
    """
    analysis = analyze_debug_context(debug_context)
    timestamps = debug_context.get_formatted_timestamps()

    report = f"""
# Translation Debug Report

## Session Summary
- Session ID: {debug_context.session_id}
- Source Language: {debug_context.source_language}
- YAML Mode: {debug_context.is_yaml}
- Start Time: {timestamps["start_time"]}
- End Time: {timestamps["end_time"]}
- Duration: {timestamps["duration"]}
- Iterations: {debug_context.current_iteration}/{debug_context.max_iterations}
- Final Status: {debug_context.get_final_status()}

## Performance Metrics
- Average iteration time: {analysis["performance_metrics"]["avg_iteration_time"]:.2f} seconds
- Success rate: {analysis["performance_metrics"]["success_rate"]:.2%}
- Total conversation chars: {analysis["conversation_analysis"]["total_prompt_chars"] + analysis["conversation_analysis"]["total_response_chars"]:,}

## Error Analysis
- Total errors: {analysis["error_patterns"]["total_errors"]}
- Error types: {", ".join(analysis["error_patterns"]["error_types"].keys())}

## Iteration Breakdown"""

    for iteration in analysis["iteration_breakdown"]:
        status = (
            "✓ Success"
            if iteration["attempt_result"]
            and iteration["attempt_result"].verification_success
            else "✗ Failed"
        )
        errors = (
            f" ({', '.join(iteration['error_types'])})"
            if iteration["error_types"]
            else ""
        )

        # Add timing information for each iteration if available
        timing_info = ""
        if iteration["attempt_result"]:
            attempt_time = iteration["attempt_result"].timestamp.strftime(
                "%H:%M:%S.%f"
            )[:-3]
            timing_info = f" at {attempt_time}"

        report += (
            f"\n- Iteration {iteration['iteration']}: {status}{errors}{timing_info}"
        )

    # Add detailed timing breakdown
    if debug_context.conversation_exchanges:
        report += "\n\n## Timing Breakdown"
        for i, exchange in enumerate(debug_context.conversation_exchanges):
            exchange_time = exchange.timestamp.strftime("%H:%M:%S.%f")[:-3]
            report += f"\n- Exchange {i + 1}: {exchange_time} ({exchange.prompt_length + exchange.response_length} chars)"

    return report
