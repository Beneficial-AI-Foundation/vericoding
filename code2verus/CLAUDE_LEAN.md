# CLAUDE_LEAN.md

This file provides guidance to Claude Code (claude.ai/code) when working with Lean to Verus translation in this repository.

## Project Overview

This is a Lean to Verus translation project that uses PydanticAI to convert Lean 4 examples to [Verus](https://verus-lang.github.io/verus/guide/overview.html) code. The project is a Python package that serves as a specialized translator for formal verification code.

## Development Environment

The project uses Nix for reproducible development environments:

- **Setup**: Use `nix develop` to enter the development shell
- **Dependencies**: Managed through `nix/buildInputs.nix` which includes:
  - `uv` (Python package manager)
  - `lefthook` (Git hooks)
  - `claude-code` (CLI tool)
  - `cargo` (Rust toolchain for Verus)

## Key Commands

- **Run the tool**: `uv run code2verus --language lean` (calls the main function for Lean translation)
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

3. **Translation Prompts**: `config.yml` contains language-specific system prompts that define:
   - Translation rules from Lean 4 to Verus
   - Semantic preservation requirements
   - Code formatting standards
   - Example translations

### Translation Process

The system prompt for Lean defines comprehensive translation rules:

- **Theorems**: `theorem` statements are converted to `proof fn` with appropriate pre/postconditions
- **Data Types**: Maps Lean structures and inductive types to Verus equivalents
- **Proofs**: Converts Lean proof tactics to Verus proof assertions
- **Functions**: Translates `def` to `fn` or `spec fn` appropriately
- **Ghost Code**: Handles Lean's computational vs. proof content distinction

### Key Paths

- `verus-x86-linux/verus`: Verus verification binary
- `config.yml`: Contains language-specific translation system prompts
- `src/code2verus/`: Main Python package
- `pyproject.toml`: Defines package metadata and the `code2verus` script entry point

## Translation Standards

When working with Lean to Verus translations:

1. Always use `use vstd::prelude::*;` at the top
2. Wrap code in `verus! { ... }` blocks
3. Use `spec fn` for pure functions, `fn` for executable code
4. Preserve logical structure and theorem statements as proof functions
5. Use snake_case for identifiers (convert from Lean's camelCase)
6. Map Lean tactics to appropriate Verus proof constructs
7. Include comments mapping back to original Lean code

## Lean 4 to Verus Mapping

Key translation patterns for Lean 4:

- `theorem` → `proof fn` with appropriate specifications
- `def` → `fn` or `spec fn` depending on computability
- `structure` → `struct` with appropriate ghost/exec fields
- `inductive` → `enum` or `struct` depending on complexity
- Lean tactics → Verus proof assertions and `by` blocks
- `have` statements → local assertions in proof context

## Development Notes

- The project uses Python 3.13+ with dependencies managed by `uv`
- Lean-specific prompts are stored in the `config.yml` under the `lean` key
- Verus toolchain is included locally in `verus-x86-linux/`
- The project follows Nix-based development practices with flakes
