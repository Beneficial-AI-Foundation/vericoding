#!/usr/bin/env python3
"""
Claude Session Wrapper for capturing conversation traces.
"""

import json
from typing import Dict, Optional, List, Any
from claude_code_sdk import ClaudeCodeSession, ClaudeCodeMessage

from vericoding.tools.trace_logger import get_trace_logger


class TrackedClaudeSession:
    """Wrapper around ClaudeCodeSession that captures conversation traces."""
    
    def __init__(self, experiment_id: str, trace_logger=None):
        """
        Initialize tracked session.
        
        Args:
            experiment_id: Unique ID for this experiment
            trace_logger: Optional trace logger instance (uses global if not provided)
        """
        self.experiment_id = experiment_id
        self.trace_logger = trace_logger or get_trace_logger()
        self.session = ClaudeCodeSession()
        self.turn_count = 0
    
    def send_message(self, prompt: str, metadata: Optional[Dict[str, Any]] = None) -> ClaudeCodeMessage:
        """
        Send a message and capture the full exchange.
        
        Args:
            prompt: The prompt to send
            metadata: Optional metadata about this turn
        
        Returns:
            Claude's response
        """
        self.turn_count += 1
        
        # Send message through actual session
        response = self.session.send_message(prompt)
        
        # Extract tools used from response if available
        tools_used = self._extract_tools_from_response(response)
        
        # Log the turn
        self.trace_logger.add_turn(
            experiment_id=self.experiment_id,
            prompt=prompt,
            response=response.text,
            tools_used=tools_used,
            metadata={
                "turn_number": self.turn_count,
                **(metadata or {})
            }
        )
        
        return response
    
    def _extract_tools_from_response(self, response: ClaudeCodeMessage) -> List[Dict[str, Any]]:
        """Extract tool usage information from Claude's response."""
        tools = []
        
        # Parse response for MCP tool usage patterns
        # This is a simplified version - in practice, we'd parse the actual tool calls
        response_text = response.text
        
        # Look for common MCP tool patterns
        mcp_tools = [
            "lean_goal", "lean_diagnostic_messages", "lean_hover_info",
            "lean_completions", "lean_declaration_file", "lean_multi_attempt",
            "lean_run_code", "lean_leansearch", "lean_loogle", 
            "lean_state_search", "lean_hammer_premise", "lean_build",
            "lean_file_contents", "lean_term_goal"
        ]
        
        for tool in mcp_tools:
            if tool in response_text:
                tools.append({
                    "name": tool,
                    "type": "mcp_tool",
                    "parameters": {}  # Would extract actual params in full implementation
                })
        
        # Look for file operations
        if "Reading file" in response_text or "Writing file" in response_text:
            tools.append({
                "name": "file_operation",
                "type": "system_tool",
                "parameters": {}
            })
        
        return tools
    
    def close(self):
        """Close the session."""
        # ClaudeCodeSession might not have a close method, but we add for consistency
        pass


def create_tracked_session(experiment_id: str, file_name: str, 
                         language: str, use_mcp: bool,
                         metadata: Optional[Dict[str, Any]] = None) -> TrackedClaudeSession:
    """
    Create a tracked Claude session and start a trace.
    
    Args:
        experiment_id: Unique experiment ID
        file_name: Name of the file being processed
        language: Programming language
        use_mcp: Whether MCP tools are enabled
        metadata: Additional metadata
    
    Returns:
        TrackedClaudeSession instance
    """
    trace_logger = get_trace_logger()
    
    # Start the trace
    trace_logger.start_trace(
        experiment_id=experiment_id,
        file_name=file_name,
        language=language,
        use_mcp=use_mcp,
        metadata=metadata
    )
    
    return TrackedClaudeSession(experiment_id, trace_logger)