"""VeriCoding package for specification-to-code generation across multiple verification languages."""

__version__ = "0.1.0"

# Import key components for easier access
from vericoding.common.prompt_loader import BasePromptLoader

__all__ = ["BasePromptLoader"]


def main() -> None:
    print("Hello from vericoding!")
