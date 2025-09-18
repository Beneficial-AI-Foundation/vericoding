"""
Modern Lean verification agent using Claude Code SDK.
"""
import os
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from enum import Enum
import json
import time

from claude_code_sdk import ClaudeCodeSession, ClaudeCodeMessage
from pydantic import BaseModel

from .prompts import LeanPromptConfig, PromptType, MCPTool, LeanPromptManager


class VerificationStatus(str, Enum):
    """Status of Lean file verification."""
    SUCCESS = "success"
    ERROR = "error"
    TIMEOUT = "timeout"
    NOT_STARTED = "not_started"


@dataclass
class VerificationResult:
    """Result of a Lean verification attempt."""
    status: VerificationStatus
    output: str
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    duration: float = 0.0
    
    @property
    def success(self) -> bool:
        return self.status == VerificationStatus.SUCCESS


@dataclass
class AgentState:
    """State maintained by the Lean agent."""
    spec_file: Path
    current_code: str
    iterations: List[Dict[str, Any]] = field(default_factory=list)
    verification_results: List[VerificationResult] = field(default_factory=list)
    mcp_tools_used: List[str] = field(default_factory=list)
    success: bool = False
    final_code: Optional[str] = None


class LeanAgent:
    """Modern Lean verification agent with Claude Code SDK integration."""
    
    def __init__(self, use_mcp: bool = True, max_iterations: int = 5):
        """Initialize the Lean agent.
        
        Args:
            use_mcp: Whether to use MCP tools
            max_iterations: Maximum verification attempts
        """
        self.use_mcp = use_mcp
        self.max_iterations = max_iterations
        self.prompt_manager = LeanPromptManager()
        self.session = None
        self.lean_path = os.getenv("LEAN_PATH", "lean")
    
    def _init_session(self) -> ClaudeCodeSession:
        """Initialize Claude Code session."""
        if self.session is None:
            self.session = ClaudeCodeSession()
        return self.session
    
    def _extract_lean_code(self, response: str) -> str:
        """Extract Lean code from Claude's response."""
        import re
        
        # Look for code blocks marked with ```lean
        lean_code_pattern = r'```lean\s*\n(.*?)\n```'
        match = re.search(lean_code_pattern, response, re.DOTALL)
        
        if match:
            return match.group(1).strip()
        
        # If no ```lean block, try generic code block
        code_pattern = r'```\s*\n(.*?)\n```'
        match = re.search(code_pattern, response, re.DOTALL)
        
        if match:
            return match.group(1).strip()
        
        # Return as-is if no code blocks found
        return response.strip()
    
    def verify_lean_file(self, file_path: Path) -> VerificationResult:
        """Verify a Lean file using the Lean compiler.
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            VerificationResult with status and output
        """
        start_time = time.time()
        
        try:
            result = subprocess.run(
                [self.lean_path, str(file_path)],
                capture_output=True,
                text=True,
                timeout=120
            )
            
            duration = time.time() - start_time
            
            # Parse output for errors and warnings
            output = result.stdout + '\n' + result.stderr
            errors = []
            warnings = []
            
            for line in output.split('\n'):
                if 'error:' in line.lower():
                    errors.append(line)
                elif 'warning:' in line.lower():
                    warnings.append(line)
            
            status = VerificationStatus.SUCCESS if result.returncode == 0 else VerificationStatus.ERROR
            
            return VerificationResult(
                status=status,
                output=output,
                errors=errors,
                warnings=warnings,
                duration=duration
            )
            
        except subprocess.TimeoutExpired:
            return VerificationResult(
                status=VerificationStatus.TIMEOUT,
                output="Verification timed out after 120 seconds",
                duration=120.0
            )
        except Exception as e:
            return VerificationResult(
                status=VerificationStatus.ERROR,
                output=str(e),
                duration=time.time() - start_time
            )
    
    def verify_with_mcp(self, file_path: Path) -> VerificationResult:
        """Verify using MCP tools through Claude Code SDK.
        
        Args:
            file_path: Path to the Lean file
            
        Returns:
            VerificationResult with enhanced error analysis
        """
        session = self._init_session()
        
        prompt = f"""
Please verify this Lean file using the lean-lsp-mcp tools:

File: {file_path}

Use these tools in sequence:
1. lean_file_contents to read the file
2. lean_diagnostic_messages to get all diagnostic messages
3. If there are errors, use lean_goal at error locations to understand the proof state
4. lean_build if needed to ensure the project builds

Provide a structured analysis of:
- Whether the file verifies successfully
- Any errors with line numbers and explanations
- Any warnings
- Suggestions for fixes if there are errors
"""
        
        start_time = time.time()
        response = session.send_message(prompt)
        duration = time.time() - start_time
        
        # Parse the response to extract verification status
        response_text = response.text.lower()
        
        if "no errors" in response_text or "successfully verified" in response_text:
            status = VerificationStatus.SUCCESS
        else:
            status = VerificationStatus.ERROR
        
        # Extract errors and warnings from the response
        errors = []
        warnings = []
        
        # Simple parsing - could be enhanced with more sophisticated analysis
        lines = response.text.split('\n')
        for line in lines:
            if 'error' in line.lower() and ':' in line:
                errors.append(line.strip())
            elif 'warning' in line.lower() and ':' in line:
                warnings.append(line.strip())
        
        return VerificationResult(
            status=status,
            output=response.text,
            errors=errors,
            warnings=warnings,
            duration=duration
        )
    
    def generate_code(self, spec_code: str, iteration: int = 0) -> str:
        """Generate Lean code from specification.
        
        Args:
            spec_code: The specification code with 'sorry'
            iteration: Current iteration number
            
        Returns:
            Generated Lean code
        """
        session = self._init_session()
        
        # Create prompt configuration
        config = LeanPromptConfig(
            type=PromptType.GENERATE,
            code=spec_code,
            iteration=iteration,
            max_iterations=self.max_iterations,
            use_mcp=self.use_mcp,
            mcp_tools=self.prompt_manager.get_mcp_tools_for_stage("generate") if self.use_mcp else []
        )
        
        prompt = self.prompt_manager.create_prompt(config)
        response = session.send_message(prompt)
        
        # Track MCP tool usage
        if self.use_mcp:
            # Parse response for tool usage (simplified - could be enhanced)
            tools_mentioned = [tool.value for tool in MCPTool if tool.value in response.text]
            for tool in tools_mentioned:
                if tool not in self.state.mcp_tools_used:
                    self.state.mcp_tools_used.append(tool)
        
        return self._extract_lean_code(response.text)
    
    def fix_code(self, code: str, error_details: str, iteration: int) -> str:
        """Fix verification errors in Lean code.
        
        Args:
            code: Current Lean code
            error_details: Error messages from verification
            iteration: Current iteration number
            
        Returns:
            Fixed Lean code
        """
        session = self._init_session()
        
        # Create prompt configuration
        config = LeanPromptConfig(
            type=PromptType.FIX,
            code=code,
            error_details=error_details,
            iteration=iteration,
            max_iterations=self.max_iterations,
            use_mcp=self.use_mcp,
            mcp_tools=self.prompt_manager.get_mcp_tools_for_stage("fix") if self.use_mcp else []
        )
        
        prompt = self.prompt_manager.create_prompt(config)
        response = session.send_message(prompt)
        
        return self._extract_lean_code(response.text)
    
    def process_spec_file(self, spec_file: Path) -> AgentState:
        """Process a specification file to generate verified Lean code.
        
        Args:
            spec_file: Path to the specification file
            
        Returns:
            AgentState with results
        """
        # Initialize state
        self.state = AgentState(spec_file=spec_file, current_code="")
        
        # Read specification
        with open(spec_file, 'r', encoding='utf-8') as f:
            spec_code = f.read()
        
        # Generate initial implementation
        print(f"Generating initial implementation for {spec_file.name}...")
        self.state.current_code = self.generate_code(spec_code, iteration=0)
        
        # Iterative refinement
        for iteration in range(1, self.max_iterations + 1):
            print(f"Iteration {iteration}/{self.max_iterations}...")
            
            # Write code to temporary file
            temp_file = spec_file.parent / f"{spec_file.stem}_temp.lean"
            with open(temp_file, 'w', encoding='utf-8') as f:
                f.write(self.state.current_code)
            
            # Verify
            if self.use_mcp:
                result = self.verify_with_mcp(temp_file)
            else:
                result = self.verify_lean_file(temp_file)
            
            self.state.verification_results.append(result)
            
            # Record iteration
            self.state.iterations.append({
                "iteration": iteration,
                "verification_status": result.status.value,
                "duration": result.duration,
                "errors": len(result.errors),
                "warnings": len(result.warnings)
            })
            
            if result.success:
                print(f"✓ Verification successful!")
                self.state.success = True
                self.state.final_code = self.state.current_code
                break
            else:
                print(f"✗ Verification failed with {len(result.errors)} errors")
                
                if iteration < self.max_iterations:
                    print("Attempting to fix errors...")
                    self.state.current_code = self.fix_code(
                        self.state.current_code,
                        result.output,
                        iteration
                    )
            
            # Clean up temp file
            temp_file.unlink(missing_ok=True)
        
        return self.state
    
    def get_summary(self) -> Dict[str, Any]:
        """Get a summary of the agent's work."""
        if not hasattr(self, 'state'):
            return {"error": "No processing has been done yet"}
        
        return {
            "spec_file": str(self.state.spec_file),
            "success": self.state.success,
            "iterations": len(self.state.iterations),
            "mcp_tools_used": self.state.mcp_tools_used,
            "total_errors": sum(r.errors for r in self.state.verification_results),
            "total_warnings": sum(r.warnings for r in self.state.verification_results),
            "final_verification": self.state.verification_results[-1].status.value if self.state.verification_results else "not_started"
        }


# Convenience function for command-line usage
def run_lean_agent(spec_file: Path, use_mcp: bool = True, max_iterations: int = 5) -> Dict[str, Any]:
    """Run the Lean agent on a specification file.
    
    Args:
        spec_file: Path to the Lean specification file
        use_mcp: Whether to use MCP tools
        max_iterations: Maximum verification attempts
        
    Returns:
        Summary of the agent's work
    """
    agent = LeanAgent(use_mcp=use_mcp, max_iterations=max_iterations)
    state = agent.process_spec_file(spec_file)
    
    # Save final code if successful
    if state.success and state.final_code:
        output_file = spec_file.parent / f"{spec_file.stem}_impl.lean"
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(state.final_code)
        print(f"Final implementation saved to {output_file}")
    
    return agent.get_summary()