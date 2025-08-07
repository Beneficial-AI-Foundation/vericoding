# CLAUDE_DAFNY.md

This file provides guidance to Claude Code (claude.ai/code) when working with Dafny to Verus translation in this repository.

## Project Overview

This is a Dafny to Verus translation project that uses PydanticAI to convert [DafnyBench](https://huggingface.co/datasets/wendy-sun/DafnyBench) examples to [Verus](https://verus-lang.github.io/verus/guide/overview.html) code. The project is a Python package that serves as a specialized translator for formal verification code.

## Development Environment

The project uses Nix for reproducible development environments:

- **Setup**: Use `nix develop` to enter the development shell
- **Dependencies**: Managed through `nix/buildInputs.nix` which includes:
  - `uv` (Python package manager)
  - `lefthook` (Git hooks)
  - `claude-code` (CLI tool)
  - `dafny` (Dafny language tools)
  - `cargo` (Rust toolchain for Verus)

## Key Commands

- **Run the tool**: `uv run code2verus --language dafny` (calls the main function for Dafny translation)
- **Install dependencies**: `uv sync`
- **Format code**: `nix fmt` (uses treefmt-nix configuration)
- **Verify Verus code**: `verus <file.rs>`

## Architecture

### Core Components

1. **Translation Engine**: Located in `src/code2verus/__init__.py`
   - Parametric translation engine with language-specific prompts
   - Designed to use PydanticAI for intelligent code translation

2. **Verus Runtime**: The `verus-x86-linux/` directory contains:
   - Verus verification engine (`verus` binary)
   - Standard library (`vstd/`)
   - Built-in modules (`builtin/`, `builtin_macros/`)
   - State machine macros (`state_machines_macros/`)

3. **Translation Prompts**: `prompts.yml` contains the system prompt that defines:
   - Translation rules from Dafny to Verus
   - Semantic preservation requirements
   - Code formatting standards
   - Example translations

### Translation Process

The system prompt in `prompts.yml` defines comprehensive translation rules:

- **Contracts**: `requires`/`ensures`/`invariant` clauses are preserved
- **Data Types**: Maps Dafny collections (`seq`, `map`, `set`) to Verus equivalents
- **Proofs**: Converts `lemma` to `proof fn` and `assert` statements
- **Functions**: Translates `method` to `fn` or `proof fn` appropriately
- **Ghost Code**: Handles ghost variables and verification-only code

### Key Paths

- `verus-x86-linux/verus`: Verus verification binary
- `prompts.yml`: Contains the translation system prompt
- `src/code2verus/`: Main Python package
- `pyproject.toml`: Defines package metadata and the `code2verus` script entry point

## Translation Standards

When working with translations, follow the patterns defined in `prompts.yml`:

1. Always use `use vstd::prelude::*;` at the top
2. Wrap code in `verus! { ... }` blocks
3. Use `spec fn` for pure functions, `fn` for executable code
4. Preserve logical contracts and proof structure
5. Use snake_case for identifiers
6. Include comments mapping back to original Dafny code

## Development Notes

- The project uses Python 3.13+ with dependencies managed by `uv`
- The codebase is currently minimal and appears to be in early development
- Verus toolchain is included locally in `verus-x86-linux/`
- The project follows Nix-based development practices with flakes
