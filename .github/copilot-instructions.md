# VeriCoding Project - GitHub Copilot Custom Instructions

## Project Overview
This is **VeriCoding**, a verification-focused coding project specializing in Lean 4 formal verification experiments with Model Context Protocol (MCP) integration for enhanced development workflows.

## Core Technologies & Tools
- **Primary Language**: Lean 4 for formal verification and proof development
- **MCP Integration**: lean-lsp-mcp, LeanExplore for real-time feedback and theorem search
- **Python**: Secondary language using `uv` package manager (NOT pip)
- **Version Control**: Jujutsu (jj) preferred over git for development workflow
- **Build System**: `lake build` for Lean projects

## Development Philosophy
**"Pit of Success"**: Build internal systems that grow outward, preventing the fallible external world from leaking in except at well-defined boundaries. Write tooling/linters/auto-fixers to guide future users (including AI) toward correct solutions.

**Programming Principles**:
- Onomastics (naming), composition (functoriality), and caching
- Statically typed functional programming with mutability where sensible
- Conformally thinking at every scale and across scales

## Lean 4 Development Guidelines

### Core Practices
- **Sorry-friendly programming**: Use specifications with `sorry` instead of comments - the typechecker uses these for program generation
- **Named holes**: Use `?holeName` for incremental development of well-typed fragment programs  
- **Decompose proofs**: Break down until `canonical`, `grind`, and `simp` can dissolve the pieces
- **Build frequently**: Spam `lake build` to verify pieces work and build up functorially

### Variable Naming Conventions
- Use `r`(ow) and `c`(olumn) instead of generic `i` and `j`
- Use `R` and `C` for matrix dimensions instead of `m` and `n`
- Prefer semantic names over mathematical conventions

### Code Structure
- **Imports MUST come first**: Before any syntax elements, including module/doc comments
- Wrap reserved names in «guillemets» when needed
- Implement "notation typeclasses" like `GetElem`, `Add`, etc where appropriate
- Use multiline comments instead of docstrings to avoid parsing errors

### Common Pitfalls to Avoid
- Automatic implicit parameters issues
- Using `have` for data instead of `let`
- Rewriting under binders
- Using `b > a` instead of `a < b` (prefer ascending order)
- Confusing `Prop` and `Bool`
- Natural number subtraction edge cases
- Division by zero in specifications

## Python Development Standards
- **ALWAYS use `uv`** for package management, NOT pip
- Use `uv add` over `uv pip install`
- Use `uv sync` and `uv run` over direct python execution
- Use hatch for build integration in `pyproject.toml`

## MCP Tools Integration
This project uses Model Context Protocol tools for enhanced Lean development:

### Available Tools
- `lean_diagnostic_messages`: Get errors, warnings, infos for Lean files
- `lean_goal`: Get proof goals/state at specific locations (crucial for proof development)
- `lean_term_goal`: Get expected types at locations
- `lean_hover_info`: Get documentation for symbols
- `lean_completions`: Code auto-completion
- `lean_multi_attempt`: Try multiple code snippets and get diagnostics
- Search tools: `lean_leansearch`, `lean_loogle`, `lean_state_search`, `lean_hammer_premise`

### LeanExplore Tools
- `mcp__leanexplore__search`: Search Lean statement groups
- `mcp__leanexplore__get_by_id`: Retrieve statement groups by ID
- `mcp__leanexplore__get_dependencies`: Get dependencies

## Build & Development Commands
```bash
# Lean development
lake build              # Primary build command - use frequently
lake build --verbose    # Verbose output for debugging
lake clean              # Clean build artifacts

# Python development
uv sync                 # Sync dependencies
uv run <script>         # Run Python scripts
uv add <package>        # Add dependencies
```

## Version Control Preferences
- **Jujutsu (jj)** preferred over git
- Use `jj git fetch` + `jj rebase -d main` instead of `git pull`
- `jj absorb` for automatic squashing into relevant commits
- `jj undo` and `jj op restore` for history manipulation
- Anonymous branches - no need to name every small change

## File Organization
- `.mcp.json`: MCP server configuration
- `lakefile.lean`: Lean build configuration (preferred over lakefile.toml)
- `CLAUDE.md`: Comprehensive project documentation and guidelines
- Set `linter.missingDocs = true` and `relaxedAutoImplicit = false` in lakefile.lean

## Code Quality Standards
- Use `rg` and `fd` instead of grep/find
- Make atomic commits and use branches liberally
- Write tests that validate minimal changes
- Use extensible error messages and compiler tooling for "pit of success"
- If solving hard problems, write tactics or simprocs to pave the way

## AI Assistance Guidelines
When providing code suggestions:
1. Prioritize Lean 4 verification and formal proof development
2. Suggest MCP tool usage for real-time feedback during development
3. Recommend `lake build` after significant changes
4. Follow sorry-friendly programming patterns
5. Use proper variable naming conventions
6. Suggest `uv` commands for Python package management
7. Consider jj workflow over git when suggesting version control operations
8. Reference common Lean pitfalls and suggest alternatives
9. Recommend decomposing complex proofs into smaller, tool-solvable pieces