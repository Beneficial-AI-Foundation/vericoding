"""Agent creation and translation logic for code2verus"""
from pydantic_ai import Agent
import logfire

from code2verus.config import system_prompt, cfg
from code2verus.tools import verus_tool, dafny_tool
from code2verus.utils import extract_rust_code


def create_agent(source_language: str = "dafny"):
    """Create and return a configured PydanticAI agent with tools"""
    # Load language-specific system prompt
    language_prompt = cfg.get("system_prompts", {}).get(source_language.lower(), system_prompt)
    
    return Agent(
        cfg["model"],
        name="code2verus",
        deps_type=str,
        output_type=str,
        tools=[verus_tool, dafny_tool],
        system_prompt=language_prompt,
        retries=10,
    )


async def translate_code_to_verus(source_code: str, source_language: str = "dafny", is_yaml: bool = False) -> tuple[str, int]:
    """Translate source code to Verus using the agent"""
    agent = create_agent(source_language)

    yaml_prompt = f"""\
        The YAML file contains {source_language} code split into segments. Your job is to translate each of them to its corresponding Verus code while maintaining the YAML structure.

        Make sure the preamble starts with `use vstd::prelude::*;`, immediately followed by a `verus!` block, which starts in the preamble, and closes in the postamble, containing `fn main()`.

        IMPORTANT: In your response, include the final YAML file containing Verus code in a code block marked with ```verus. Do not include explanations or summaries in the code block - only the executable Verus code.    
        """

    default_prompt = f"""\
        Use the `verus` tool to make sure your output compiles. 

        IMPORTANT: In your response, include the final Verus code in a code block marked with ```rust or ```verus. Do not include explanations or summaries in the code block - only the executable Verus code.
        """

    prompt = yaml_prompt if is_yaml else default_prompt

    user_prompt = f"""
Please translate the following {source_language} code to Verus:

```{source_language.lower()}
{source_code}
```

{prompt}  
"""

    result = await agent.run(user_prompt, deps=source_code)

    # Extract only the Rust code from the agent's output
    rust_code = extract_rust_code(result.output)
    num_iterations = len(result.all_messages()) // 3

    return rust_code, num_iterations
