"""
Pydantic-based prompt system for Lean verification experiments.
"""
from pydantic import BaseModel, Field
from typing import Optional, List, Dict, Any, Literal
from enum import Enum
from jinja2 import Template
from pathlib import Path
import yaml


class PromptType(str, Enum):
    """Types of prompts available for Lean verification."""
    GENERATE = "generate_code"
    FIX = "fix_verification"
    ANALYZE_ERROR = "analyze_error"
    USE_MCP_TOOLS = "use_mcp_tools"


class MCPTool(str, Enum):
    """Available MCP tools for Lean verification."""
    LEAN_GOAL = "lean_goal"
    LEAN_DIAGNOSTIC = "lean_diagnostic_messages"
    LEAN_HOVER = "lean_hover_info"
    LEAN_COMPLETIONS = "lean_completions"
    LEAN_DECLARATION = "lean_declaration_file"
    LEAN_MULTI_ATTEMPT = "lean_multi_attempt"
    LEAN_LEANSEARCH = "lean_leansearch"
    LEAN_LOOGLE = "lean_loogle"
    LEAN_STATE_SEARCH = "lean_state_search"
    LEAN_HAMMER = "lean_hammer_premise"
    LEAN_BUILD = "lean_build"
    LEAN_FILE_CONTENTS = "lean_file_contents"
    LEAN_TERM_GOAL = "lean_term_goal"


class LeanPromptConfig(BaseModel):
    """Configuration for a Lean prompt."""
    type: PromptType
    code: str
    error_details: Optional[str] = None
    iteration: int = 0
    max_iterations: int = 5
    use_mcp: bool = False
    mcp_tools: List[MCPTool] = Field(default_factory=list)
    include_examples: bool = False
    temperature: float = 0.0
    
    class Config:
        use_enum_values = True


class GenerateCodePrompt(BaseModel):
    """Prompt for generating Lean code from specifications."""
    
    TEMPLATE = Template("""The task is to generate a Lean file that is verified from an incomplete Lean file that contains the keyword "sorry" in place of desired code and proof blocks.

INPUT: a Lean file of the form
       def def_type_1 := sorry     
       ...
       def def_type_n := sorry
       theorem thm_type_1 := sorry
       ...
       theorem thm_type_n := sorry
  WHERE:
  - where each def_type_i is of the form 
    name {implicit_args} (hypotheses) (arguments) : result
    where "sorry" represents a missing implementation for a desired function.

  - each theorem represents a property about one or more of the def_type_i.

{% if use_mcp %}
You have access to these MCP tools to help understand the code:
{% for tool in mcp_tools %}
- {{ tool }}: {{ tool_descriptions[tool] }}
{% endfor %}

Use these tools proactively to:
1. Check proof states with lean_goal
2. Search for relevant theorems with lean_leansearch or lean_loogle
3. Get documentation with lean_hover_info
4. Understand error messages with lean_diagnostic_messages
{% endif %}

OUTPUT: Return ONLY the complete Lean code file, wrapped in a ```lean code block. Do not include any explanations, reasoning, or markdown outside the code block.

The output should be a verified Lean file of the form:
      def def_type_1 := implementation_1
      ...
      def def_type_n := implementation_n
      theorem thm_type_1 := proof_1
      ...
      theorem thm_type_n := proof_n
  
CRITICAL RULES:
- do not change any of def_type_i or thm_type_i 
- do not use sorry in the output file
- the input file may contain additional definitions (without "sorry") that you can use
- you can add helper definitions, theorems, and lemmas as needed
- for any new definition, lemma or theorem you add, add a comment -- LLM HELPER
- Return ONLY the Lean code, no explanations or markdown

{% if iteration > 0 %}
Note: This is iteration {{ iteration }} of {{ max_iterations }}. Previous attempts have failed.
Focus on addressing the specific issues from the error messages.
{% endif %}

LEAN SPECIFICATION WITH EMPTY DEFINITIONS AND PROOF BODIES:
{{ code }}""")
    
    tool_descriptions: Dict[str, str] = {
        MCPTool.LEAN_GOAL: "Check proof state at specific locations",
        MCPTool.LEAN_DIAGNOSTIC: "Get all diagnostic messages for the file",
        MCPTool.LEAN_HOVER: "Get documentation for symbols",
        MCPTool.LEAN_COMPLETIONS: "Get code completions",
        MCPTool.LEAN_LEANSEARCH: "Search theorems using natural language",
        MCPTool.LEAN_LOOGLE: "Search by type signature or pattern",
        MCPTool.LEAN_STATE_SEARCH: "Search based on current proof state",
        MCPTool.LEAN_BUILD: "Build the Lean project"
    }
    
    def render(self, config: LeanPromptConfig) -> str:
        """Render the prompt with the given configuration."""
        return self.TEMPLATE.render(
            code=config.code,
            use_mcp=config.use_mcp,
            mcp_tools=config.mcp_tools,
            tool_descriptions=self.tool_descriptions,
            iteration=config.iteration,
            max_iterations=config.max_iterations
        )


class FixVerificationPrompt(BaseModel):
    """Prompt for fixing verification errors."""
    
    TEMPLATE = Template("""The task is to review definitions and theorems in a Lean file that do not verify due to missing or invalid implementations or proofs.

INPUT: a Lean file that contains some definitions and theorems that don't verify.
The file contains:
- some atoms (def, lemma, theorem, ...) with comment -- LLM HELPER that you can change/remove
- other atoms where you can only change the implementation/proof body

{% if use_mcp %}
IMPORTANT: Use these MCP tools to understand and fix the errors:
{% for tool in mcp_tools %}
- {{ tool }}: {{ tool_descriptions[tool] }}
{% endfor %}

Specifically:
1. Use lean_goal to check the proof state where errors occur
2. Use lean_hover_info to understand unfamiliar terms
3. Use lean_leansearch or lean_loogle to find relevant theorems
4. Use lean_state_search to find theorems that match your goal
{% endif %}

POSITIVE CRITICAL RULES:
- you can change the implementation/proof to fix verification errors
- you can add helper definitions with comment -- LLM HELPER
  
NEGATIVE CRITICAL RULES:
- do not use sorry in the output file
- output valid Lean code
- Return ONLY the Lean code, no explanations or markdown

OUTPUT: Return ONLY the complete Lean code file, wrapped in a ```lean code block.

ERROR DETAILS from Lean verification:
{{ error_details }}

{% if iteration > 1 %}
Iteration {{ iteration }}/{{ max_iterations }}: Focus on the specific error locations.
{% if use_mcp %}
Use lean_goal at the error line numbers to understand what's needed.
{% endif %}
{% endif %}

Code Below:
{{ code }}""")
    
    tool_descriptions: Dict[str, str] = GenerateCodePrompt.tool_descriptions
    
    def render(self, config: LeanPromptConfig) -> str:
        """Render the prompt with the given configuration."""
        return self.TEMPLATE.render(
            code=config.code,
            error_details=config.error_details,
            use_mcp=config.use_mcp,
            mcp_tools=config.mcp_tools,
            tool_descriptions=self.tool_descriptions,
            iteration=config.iteration,
            max_iterations=config.max_iterations
        )


class LeanPromptManager:
    """Manager for all Lean prompts."""
    
    def __init__(self):
        self.generate_prompt = GenerateCodePrompt()
        self.fix_prompt = FixVerificationPrompt()
        
        # Load CLAUDE.md if available
        self.claude_md_content = self._load_claude_md()
    
    def _load_claude_md(self) -> Optional[str]:
        """Load CLAUDE.md file for additional context."""
        claude_md_path = Path(__file__).parent.parent.parent.parent / "CLAUDE.md"
        if claude_md_path.exists():
            with open(claude_md_path, 'r', encoding='utf-8') as f:
                return f.read()
        return None
    
    def create_prompt(self, config: LeanPromptConfig) -> str:
        """Create a prompt based on the configuration."""
        if config.type == PromptType.GENERATE:
            prompt = self.generate_prompt.render(config)
        elif config.type == PromptType.FIX:
            prompt = self.fix_prompt.render(config)
        else:
            raise ValueError(f"Unknown prompt type: {config.type}")
        
        # Add CLAUDE.md context if available
        if self.claude_md_content and config.use_mcp:
            context_header = f"# Project Context (from CLAUDE.md)\n\n{self.claude_md_content}\n\n---\n\n"
            prompt = context_header + prompt
        
        return prompt
    
    def get_mcp_tools_for_stage(self, stage: Literal["generate", "fix", "analyze"]) -> List[MCPTool]:
        """Get recommended MCP tools for a specific stage."""
        if stage == "generate":
            return [
                MCPTool.LEAN_GOAL,
                MCPTool.LEAN_LEANSEARCH,
                MCPTool.LEAN_LOOGLE,
                MCPTool.LEAN_HOVER
            ]
        elif stage == "fix":
            return [
                MCPTool.LEAN_GOAL,
                MCPTool.LEAN_DIAGNOSTIC,
                MCPTool.LEAN_STATE_SEARCH,
                MCPTool.LEAN_HOVER,
                MCPTool.LEAN_COMPLETIONS
            ]
        elif stage == "analyze":
            return [
                MCPTool.LEAN_DIAGNOSTIC,
                MCPTool.LEAN_GOAL,
                MCPTool.LEAN_FILE_CONTENTS
            ]
        else:
            return []


# Backward compatibility layer
class LegacyPromptLoader:
    """Backward compatibility with YAML-based prompts."""
    
    def __init__(self, prompts_file=None):
        self.manager = LeanPromptManager()
        
        # Load YAML if provided (for migration period)
        if prompts_file and Path(prompts_file).exists():
            with open(prompts_file, 'r') as f:
                self.yaml_prompts = yaml.safe_load(f)
        else:
            self.yaml_prompts = {}
    
    def format_prompt(self, prompt_name: str, **kwargs) -> str:
        """Format a prompt with backward compatibility."""
        if prompt_name == "generate_code":
            config = LeanPromptConfig(
                type=PromptType.GENERATE,
                code=kwargs.get('code', ''),
                use_mcp=False  # Legacy doesn't use MCP
            )
            return self.manager.create_prompt(config)
        elif prompt_name == "fix_verification":
            config = LeanPromptConfig(
                type=PromptType.FIX,
                code=kwargs.get('code', ''),
                error_details=kwargs.get('errorDetails', ''),
                use_mcp=False
            )
            return self.manager.create_prompt(config)
        else:
            # Fall back to YAML if available
            if prompt_name in self.yaml_prompts:
                return self.yaml_prompts[prompt_name].format(**kwargs)
            raise KeyError(f"Unknown prompt: {prompt_name}")