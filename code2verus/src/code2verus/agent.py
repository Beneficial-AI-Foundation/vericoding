"""Agent creation and translation logic for code2verus"""

from pydantic_ai import Agent
import logfire

from code2verus.config import system_prompt, cfg
from code2verus.tools import verus_tool, dafny_tool
from code2verus.utils import extract_rust_code


def create_agent(source_language: str = "dafny"):
    """Create and return a configured PydanticAI agent with tools"""
    # Load language-specific system prompt
    language_prompt = cfg.get("system_prompts", {}).get(
        source_language.lower(), system_prompt
    )

    return Agent(
        cfg["model"],
        name="code2verus",
        deps_type=str,
        output_type=str,
        tools=[verus_tool, dafny_tool],
        system_prompt=language_prompt,
        retries=10,
    )


async def translate_code_to_verus(
    source_code: str, source_language: str = "dafny", is_yaml: bool = False
) -> tuple[str, int]:
    """Translate source code to Verus using the agent"""
    agent = create_agent(source_language)

    # Get language-specific prompts from config
    if is_yaml:
        additional_prompt = cfg.get("yaml_instructions", {}).get(
            source_language.lower(), ""
        )
    else:
        additional_prompt = cfg.get("default_prompts", {}).get(
            source_language.lower(), ""
        )

    user_prompt = f"""
Please translate the following {source_language} code to Verus:

```{source_language.lower()}
{source_code}
```

{additional_prompt}
"""

    result = await agent.run(user_prompt, deps=source_code)

    # Extract only the Rust code from the agent's output
    rust_code = extract_rust_code(result.output)
    num_iterations = len(result.all_messages()) // 3

    return rust_code, num_iterations
