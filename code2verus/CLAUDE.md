# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a multi-language to Verus translation project that uses PydanticAI to convert formal verification code from various languages (currently Dafny and Lean 4) to [Verus](https://verus-lang.github.io/verus/guide/overview.html) code. The project is a Python package that serves as a specialized translator for formal verification languages.

**NEW**: The project now supports multiple LLM providers including OpenRouter, which provides access to 50+ models through a single API key.

## LLM Provider Support

### Direct Providers (Default)
- **Anthropic Claude**: Direct API integration (requires `ANTHROPIC_API_KEY`)
- **OpenAI GPT**: Direct API integration (requires `OPENAI_API_KEY`)
- **xAI Grok**: Direct API integration (requires `XAI_API_KEY`)

### OpenRouter Integration (NEW!)

To use OpenRouter:
1. Get API key from [openrouter.ai/keys](https://openrouter.ai/keys)
2. Set `OPENROUTER_API_KEY` environment variable
3. Update `config.yml` with an OpenRouter model (e.g., `openrouter:anthropic/claude-sonnet-4`)

## Language-Specific Documentation

- **CLAUDE_DAFNY.md**: Specific guidance for Dafny to Verus translation
- **CLAUDE_LEAN.md**: Specific guidance for Lean 4 to Verus translation

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

- **Run the tool**: 
  - Dafny: `uv run code2verus --language dafny`
  - Lean: `uv run code2verus --language lean`
- **Test OpenRouter**: `python example_openrouter.py`
- **Install dependencies**: `uv sync`
- **Format code**: `nix fmt` (uses treefmt-nix configuration)
- **Verify Verus code**: `verus <file.rs>`

## Architecture

### Core Components

1. **Translation Engine**: Located in `src/code2verus/__init__.py`
   - Parametric translation system supporting multiple source languages
   - Language-specific system prompts for different translation patterns
   - Designed to use PydanticAI for intelligent code translation

2. **Verus Runtime**: The `verus-x86-linux/` directory contains:
   - Verus verification engine (`verus` binary)
   - Standard library (`vstd/`)
   - Built-in modules (`builtin/`, `builtin_macros/`)
   - State machine macros (`state_machines_macros/`)

3. **Translation Prompts**: `config.yml` contains language-specific system prompts that define:
   - Translation rules from source languages (Dafny, Lean) to Verus
   - Semantic preservation requirements
   - Code formatting standards
   - Example translations for each supported language

### Translation Process

The system supports multiple source languages with language-specific prompts in `config.yml`:

**Dafny to Verus:**
- **Contracts**: `requires`/`ensures`/`invariant` clauses are preserved
- **Data Types**: Maps Dafny collections (`seq`, `map`, `set`) to Verus equivalents
- **Proofs**: Converts `lemma` to `proof fn` and `assert` statements
- **Functions**: Translates `method` to `fn` or `proof fn` appropriately

**Lean 4 to Verus:**
- **Theorems**: `theorem` statements converted to `proof fn` with specifications
- **Functions**: `def` mapped to `fn` or `spec fn` based on computability
- **Structures**: Lean structures translated to Verus structs
- **Tactics**: Lean proof tactics converted to Verus proof constructs

### Key Paths

- `verus-x86-linux/verus`: Verus verification binary
- `config.yml`: Contains language-specific translation system prompts
- `src/code2verus/`: Main Python package
- `pyproject.toml`: Defines package metadata and the `code2verus` script entry point

## Translation Standards

When working with translations, follow the patterns defined in `config.yml` for each language:

1. Always use `use vstd::prelude::*;` at the top
2. Wrap code in `verus! { ... }` blocks
3. Use `spec fn` for pure functions, `fn` for executable code
4. Preserve logical contracts and proof structure
5. Use snake_case for identifiers
6. Include comments mapping back to original source code
7. Follow language-specific translation patterns (see CLAUDE_DAFNY.md and CLAUDE_LEAN.md)

## Development Notes

- The project uses Python 3.13+ with dependencies managed by `uv`
- The codebase is currently minimal and appears to be in early development
- Verus toolchain is included locally in `verus-x86-linux/`
- The project follows Nix-based development practices with flakes
