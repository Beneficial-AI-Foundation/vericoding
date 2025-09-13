# Debug System Guide for code2verus

This comprehensive guide covers the complete debugging and analysis system for code2verus, including the structured debug architecture, command-line options, and analysis capabilities.

## Overview

Code2verus includes a powerful debugging system that provides comprehensive tracking, analysis, and persistence of translation sessions. This system replaces the previous dictionary-based approach with a type-safe, structured system built on Pydantic models.

### Key Features

- **Type-safe debug tracking** with Pydantic models and runtime validation
- **Comprehensive timestamping** with millisecond precision for all events
- **CLI integration** with flexible debug options
- **Rich analysis capabilities** for performance optimization
- **Structured data persistence** for later analysis
- **Real-time reporting** during translation processes

## Command-Line Debug Options

### `--save-debug`
Saves detailed debug contexts to JSON files for later analysis.

```bash
# Basic debug session saving
code2verus --save-debug

# Save to custom directory
code2verus --save-debug --debug-dir ./my_debug_sessions
```

**What it creates:**
- JSON files with descriptive names including language, status, and timestamps
- Complete conversation history, errors, and performance metrics
- Default location: `debug_sessions/debug_session_{source_lang}_to_{target_lang}_{status}_{timestamp}_{short_id}.json`

### `--debug-report`
Generates detailed debug reports after each translation.

```bash
code2verus --debug-report
```

**Example output:**
```
=== Debug Report for Item 0 ===

# Translation Debug Report

## Session Summary
- Session ID: 02acdd35-300c-41b4-a5f2-ac5a90755643
- Source Language: dafny
- Start Time: 2025-09-09 17:24:15.123
- End Time: 2025-09-09 17:25:00.456
- Duration: 45.333 seconds
- Iterations: 3/5
- Final Status: success

## Performance Metrics
- Average iteration time: 15.11 seconds
- Success rate: 100%
- Total conversation chars: 12,847

## Error Analysis
- Total errors: 2
- Error types: verification

## Iteration Breakdown
- Iteration 1: ✗ Failed (verification) at 17:24:20.234
- Iteration 2: ✗ Failed (verification) at 17:24:35.567
- Iteration 3: ✓ Success at 17:24:50.890

## Timing Breakdown
- Exchange 1: 17:24:15.234 (1,234 chars)
- Exchange 2: 17:24:35.678 (2,156 chars)
- Exchange 3: 17:24:50.912 (1,890 chars)
```

### `--debug-summary`
Prints aggregate debug summary at the end of processing.

```bash
code2verus --debug-summary --include-debug-in-result
```

**Example output:**
```
=== Overall Debug Summary ===

## Aggregate Statistics
- Total sessions: 25
- Total successful: 23 (92.0%)
- Average session duration: 34.2 seconds
- Average iterations per session: 2.1
- Total errors encountered: 15

## Performance Insights
- Most efficient sessions completed in 1 iteration
- 85% of sessions succeeded within 3 iterations
- Most common error type: verification (60%)
- Peak memory usage: ~1.2GB

## Error Patterns
- verification errors: 9 occurrences
- yaml_syntax errors: 4 occurrences  
- timeout errors: 2 occurrences
```

### `--include-debug-in-result`
Includes full debug context in translation results (uses more memory).

```bash
code2verus --include-debug-in-result
```

Required for `--debug-summary` to work properly.

### Common Usage Patterns

```bash
# Full debug mode - saves, reports, and summarizes everything
code2verus --save-debug --debug-report --debug-summary --include-debug-in-result

# Development and testing
code2verus --benchmark ./test_cases --debug-report --debug-summary

# Performance analysis
code2verus --save-debug --debug-summary --include-debug-in-result

# Production monitoring
code2verus --save-debug --debug-dir ./production_logs
```

## Structured Debug Architecture

### Core Debug Models

#### `TranslationDebugContext`
The main container for all debug information about a translation session.

```python
class TranslationDebugContext(BaseModel):
    # Session metadata
    session_id: str  # Auto-generated UUID
    original_source: str
    source_language: str
    is_yaml: bool
    max_iterations: int
    
    # Timing information
    start_time: datetime  # Auto-generated
    end_time: Optional[datetime] = None
    last_activity: Optional[datetime] = None
    
    # Translation state
    current_iteration: int = 0
    previous_attempts: List[AttemptResult] = []
    verification_errors: List[VerificationError] = []
    conversation_exchanges: List[ConversationExchange] = []
```

**Key Methods:**
- `add_attempt(attempt)`: Track a translation attempt
- `add_verification_error(error)`: Track verification failures
- `add_conversation_exchange(exchange)`: Track AI conversations
- `mark_completed()`: Mark session as finished with end timestamp
- `get_latest_error()`: Get most recent error
- `to_summary_dict()`: Generate structured summary with timing info
- `get_final_status()`: Determine final outcome

#### `ConversationExchange`
Tracks individual exchanges between the system and AI agent.

```python
class ConversationExchange(BaseModel):
    iteration: int
    prompt: str
    response: str
    prompt_length: int
    response_length: int
    message_history_length: int
    timestamp: datetime  # Auto-generated with millisecond precision
```

#### `VerificationError`
Detailed information about verification failures.

```python
class VerificationError(BaseModel):
    iteration: int
    error: str
    output: Optional[str] = None
    error_type: str = "verification"  # "verification", "yaml_syntax", etc.
    timestamp: datetime  # Auto-generated
```

#### `AttemptResult`
Comprehensive tracking of each translation attempt.

```python
class AttemptResult(BaseModel):
    iteration: int
    output_content: str
    verification_success: bool
    verification_error: Optional[str] = None
    status: IterationStatus  # SUCCESS, FAILED, YAML_ERROR, etc.
    timestamp: datetime  # Auto-generated
```

### Enhanced Timestamping

All debug data includes precise timestamping:

- **Session-level timestamps**: Start time, end time, last activity
- **Event-level timestamps**: Every conversation, error, and attempt
- **Millisecond precision**: `2025-09-09 17:24:15.123` format
- **Duration calculations**: Automatic session and iteration timing
- **Formatted output**: Human-readable timestamps in reports

## Debug Utilities and Analysis

### Save/Load Debug Sessions

```python
from code2verus.debug_utils import save_debug_context, load_debug_context

# Save debug session
filepath = save_debug_context(debug_context)
print(f"Debug session saved to: {filepath}")

# Load and analyze later
loaded_context = load_debug_context(filepath)
```

### Generate Debug Reports

```python
from code2verus.debug_utils import generate_debug_report

# Generate human-readable report with timing
report = generate_debug_report(debug_context)
print(report)
```

### Analysis Functions

```python
from code2verus.debug_utils import analyze_debug_context

analysis = analyze_debug_context(debug_context)

# Performance metrics
metrics = analysis['performance_metrics']
print(f"Success rate: {metrics['success_rate']:.2%}")
print(f"Average iteration time: {metrics['avg_iteration_time']:.2f}s")

# Error patterns
error_patterns = analysis['error_patterns']
print(f"Most common errors: {error_patterns['common_errors']}")

# Conversation analysis
conv_analysis = analysis['conversation_analysis']
print(f"Total exchanges: {conv_analysis['total_exchanges']}")
```

### Batch Analysis

```python
from pathlib import Path
from code2verus.debug_utils import load_debug_context

# Analyze all debug sessions from a directory
debug_dir = Path("debug_sessions")
sessions = []
for debug_file in debug_dir.glob("debug_session_*.json"):
    sessions.append(load_debug_context(debug_file))

# Aggregate analysis
total_duration = sum(s.to_summary_dict()['duration_seconds'] for s in sessions)
success_rate = sum(1 for s in sessions if s.get_final_status() == "success") / len(sessions)

print(f"Total processing time: {total_duration:.2f} seconds")
print(f"Overall success rate: {success_rate:.2%}")
```

## File Structure and Output

### Debug Session Files
```
debug_sessions/
├── debug_session_dafny_to_verus_success_iter3_20250910_175002_38bd434b.json
├── debug_session_verus_to_dafny_failed_iter1_20250910_174659_67d45538.json
├── debug_session_lean_to_verus_success_iter2_20250910_180125_02acdd35.json
└── ...
```

**Filename Format:**
`debug_session_{source_lang}_to_{target_lang}_{status}_iter{n}_{timestamp}_{short_id}.json`

Where:
- `{source_lang}`: Source language (e.g., `dafny`, `verus`, `lean`)
- `{target_lang}`: Target language (e.g., `verus`, `dafny`)
- `{status}`: Final session status (`success`, `failed`, `timeout`, etc.)
- `iter{n}`: Number of iterations completed (omitted if 0)
- `{timestamp}`: Creation timestamp in `YYYYMMDD_HHMMSS` format
- `{short_id}`: First 8 characters of UUID for uniqueness

This naming scheme makes it easy to:
- **Sort by time**: Timestamps ensure chronological ordering
- **Filter by language**: Quick identification of source/target languages
- **Identify outcomes**: Success/failure status immediately visible
- **Track complexity**: Iteration count indicates translation difficulty

### Translation Results
```
artifacts/
├── dafnybench/
│   ├── example1.rs
│   ├── example2.rs
│   └── success.yml
└── debug_sessions/  # When using --save-debug
    └── debug_session_*.json
```

## Performance Considerations

### Memory Usage
- **Basic debug tracking**: Minimal overhead (~1-5% increase)
- **With `--include-debug-in-result`**: Moderate increase (~10-20%)
- **Debug file saving**: Disk I/O overhead only

### Processing Time
- **Debug report generation**: ~0.1-0.5 seconds per session
- **Debug file saving**: ~0.1-0.2 seconds per session
- **Summary generation**: ~1-2 seconds for 100 sessions

### Disk Usage
- **Debug JSON files**: ~5-50KB per session
- **100 sessions**: Typically ~1-5MB total

## Migration from Old System

### Before (Dictionary-based)
```python
# Old approach - error-prone and unstructured
iteration_context = {
    "original_source": source_code,
    "verification_errors": [],
    "conversation_exchanges": [],
}

# Manual dictionary manipulation
iteration_context["verification_errors"].append({
    "iteration": 1,
    "error": "some error",
    "output": "some output"
})
```

### After (Pydantic-based)
```python
# New approach - type-safe and structured
debug_context = TranslationDebugContext(
    original_source=source_code,
    source_language="dafny",
    is_yaml=False,
    max_iterations=5
)

# Type-safe method calls
error = VerificationError(
    iteration=1,
    error="some error",
    output="some output"
)
debug_context.add_verification_error(error)
```

## Best Practices

### For Development
- Use `--debug-report` for immediate feedback
- Use `--save-debug` to build debug session collections
- Test with small benchmarks for focused debugging

### For Experiments
- Use `--debug-summary --include-debug-in-result` for aggregate stats
- Organize with `--debug-dir` by experiment
- Analyze debug files programmatically for trends

### For Production
- Use `--save-debug` only to minimize performance impact
- Analyze debug files offline rather than real-time reports
- Monitor debug summaries for performance tracking

## Troubleshooting

### Common Issues

**Debug files not being created:**
- Check write permissions in debug directory
- Ensure disk space is available
- Verify debug directory path is valid

**Memory usage too high:**
- Remove `--include-debug-in-result` flag
- Reduce `--max-concurrent` parameter
- Process smaller batches

**Debug reports not showing:**
- Ensure `--debug-report` flag is set
- Check if translations are actually running
- Verify no output redirection is hiding reports

### Getting Help

For debug system issues:
1. Check logfire logs for error messages
2. Verify debug directory permissions and disk space
3. Test with a small benchmark first
4. Review debug JSON files manually to understand structure

## Future Enhancements

Planned improvements:
- **Web dashboard** for visualizing debug data
- **Machine learning analysis** of error patterns
- **Automated optimization suggestions** based on patterns
- **Real-time monitoring** for long-running processes
- **Integration with external monitoring tools**

## Summary

The debug system provides comprehensive insights into code2verus translations through:

- **Structured, type-safe data models** for reliable debugging
- **Precise timestamping** for performance analysis
- **Flexible CLI options** for different use cases
- **Rich analysis capabilities** for optimization
- **Persistent storage** for long-term trend analysis

This enables data-driven optimization of the translation process and provides deep insights into performance patterns and failure modes.
