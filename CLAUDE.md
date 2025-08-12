# VeriCoding Project Overview

**Project Context**: This is a verification-focused coding project with Lean 4 experiments.

## Key Features

1. **Lean 4 Development Environment**: Ready for formal verification experiments
2. **MCP Integration**: Full lean-lsp-mcp tooling configured for interactive development
3. **Real-time Feedback**: Diagnostic tools, proof state inspection, and search capabilities
4. **LeanExplore**: Access to mathematical theorem databases and dependency exploration

## Lean-LSP-MCP Integration

The project is configured with Model Context Protocol (MCP) tools for enhanced Lean development. The `.mcp.json` file configures:

### MCP Servers Available

1. **lean-lsp-mcp**: Provides Lean language server protocol integration
   - Command: `uvx lean-lsp-mcp`
   - Offers real-time feedback on Lean code through various diagnostic tools

2. **leanexplore**: Search and exploration tool for Lean mathematics
   - Command: `uvx --from lean-explore leanexplore mcp serve --backend local`
   - Enables searching through Lean statement groups and dependencies

3. **LeanTool**: Additional Lean tooling
   - Located in `.mcp-tools/LeanTool`
   - Run via Poetry

4. **browsermcp**: Browser automation support
   - Command: `npx @browsermcp/mcp@latest`

### Lean LSP-MCP Tool Usage

The lean-lsp-mcp tools provide real-time feedback on your Lean code:

#### 1. `lean_diagnostic_messages`
Get all diagnostic messages (errors, warnings, infos) for a Lean file.

```text
Example output:
l20c42-l20c46, severity: 1
simp made no progress

l21c11-l21c45, severity: 1
function expected at h_empty term has type T ∩ compl T = ∅
```

#### 2. `lean_goal`
Get the proof goals (proof state) at a specific location in a Lean file. Main tool to understand proof state evolution!

```text
Example output:
Before:
S : Type u_1
inst✝¹ : Fintype S
inst✝ : Nonempty S
P : Finset (Set S)
hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅
⊢ P.card = 2 ^ (Fintype.card S - 1)
After:
no goals
```

#### 3. `lean_term_goal`
Get the expected type (term goal) at a specific location.

#### 4. `lean_hover_info`
Get hover information (documentation) for symbols at a specific location.

#### 5. `lean_completions`
Code auto-completion for available identifiers or imports.

#### 6. `lean_multi_attempt`
Try multiple Lean code snippets at a line and return goal state and diagnostics for each.

#### 7. `lean_declaration_file`
Get file contents where a symbol is declared.

#### 8. Search Tools:
- `lean_leansearch`: Natural language and Lean term search (limit: 3req/30s)
- `lean_loogle`: Search by constant, lemma name, type shape, or conclusion (limit: 3req/30s)
- `lean_state_search`: Search theorems based on proof state (limit: 3req/30s)
- `lean_hammer_premise`: Search premises using Lean Hammer (limit: 3req/30s)

### LeanExplore MCP Tools

- `mcp__leanexplore__search`: Search Lean statement groups by query
- `mcp__leanexplore__get_by_id`: Retrieve statement groups by ID
- `mcp__leanexplore__get_dependencies`: Get direct dependencies for statement groups

## General Programming Philosophy

Programming is about onomastics (naming), composition (functoriality), and caching. Think conformally at every scale and across scales.

Build a pit of success: internal systems that grow as a whole outwards, never allowing the fallible external world to leak in except at boundaries. Meet the external world at well-defined interfaces.

When solving problems, write tooling/linters/auto-fixers to widen the pit of success. Use rigid compiler error messages and linter warnings to guide future users (**including** AI) toward correct solutions.

Favor statically typed functional programming but use mutability where it makes sense or is easier to port.

## Project Structure

- `.mcp.json` - MCP server configuration for Lean development tools
- `CLAUDE.md` - This file, containing project instructions and Lean development guidelines
- Additional Lean files and experiments to be created as needed

## Development Commands

For Lean development, the key command is:
- `lake build` - Build Lean project (use frequently for constant feedback)

The lean-lsp-mcp tools are already configured in `.mcp.json` and available through the MCP interface.


## Building and Testing

```bash
# Build Lean project
lake build

# Build with verbose output for debugging
lake build --verbose

# Clean build artifacts if needed
lake clean
```

## Lean 4 Project Focus

This project is set up for Lean 4 verification experiments. The MCP tools provide:

1. **Real-time feedback** through lean-lsp-mcp diagnostic tools
2. **Proof state exploration** for understanding verification goals
3. **Search capabilities** for finding relevant theorems and lemmas
4. **Code completion** and documentation lookup

Create Lean files as needed for your verification experiments and use the MCP tools for interactive development.

## Lean 4 Development Guidelines

- Use named holes (`?foo`) for incremental development
- Wrap reserved names in «guillemets» when needed
- Implement "notation typeclasses" like `GetElem`, `Add`, etc where appropriate.
- Practice "sorry-friendly programming": Instead of a comment you put down a spec, but it is only "proved" with `sorry`. This is strictly better than a comment, because the typechecker will use it for program generation.
- **NEW: Use `plausible` before `sorry`** - The plausible tactic provides quick counterexample finding to validate assumptions before attempting full proofs. This catches spec errors early.
- Decompose proofs until tools like `canonical`, `grind`, and `simp` dissolve the pieces. Use them to do the "how", the AI should do the "what".
- Don't use `i` and `j` as variable names when you could use `r`(ow) and `c`(olumn) instead. Ditto for `m` and `n` as matrix dimensions. Use `R` and `C`.
### Import and Module Structure

- Imports MUST come before any syntax elements, including module and doc comments
  - [ ] set extensible error messages to suggest a fix for AI. Then remove this admonishment.
- Set `linter.missingDocs = true` and `relaxedAutoImplicit = false` in `lakefile.lean`.

### Common Errors and Solutions

- **"unexpected token 'namespace'"**: Module/doc comment placed incorrectly (should be after imports)
- **"unexpected token"**: Often caused by misplaced docstrings - use multiline comments instead
  - [ ] use extensible error messages to suggest a fix for AI. Then remove this admonishment.
- [ ] make a pre-push hook that runs lake build

## Python Development Guidelines

- Always use `uv` for Python package management (not pip). Use `uv add` over `uv pip install`, `uv sync`, and `uv run` over `python`. If a tool requires further build integration, use hatch to do it in the `pyproject.toml`.

## Additional Guidelines

- Use `rg` and `fd` instead of grep/find
- Make atomic commits and use branches liberally


## Development Strategies

### Lean 4 Development Approach

- Read the reference manual assiduously. Ultrathink.
- Figure out the parser by interactively building up toy components.
- [ ] install https://github.com/GasStationManager/LeanTool as mcp tool
- Spam `lake build` to verify the pieces work and build up FUNCTORIALLY.
- Use compiler tooling like extensible error messages, `simproc` (pattern guided reductions), and metaprogramming for pit of success
- If you solve a hard problem, write a tactic or simproc to pave the way
- Try harder to index without `!` or `?` - name `match`/`if` branches for better inference
- Raw string syntax: `r#".."#`, multiline strings use `\` continuation
- Use `lakefile.lean` over `lakefile.toml` for better AI introspection and metaprogramming
- Incorporate positive surprises into memories - stay curious!

### Debugging and Development Process

- Use named holes like `?holeName` for well-typed fragment programs
- Make mermaid diagrams with labeled edges describing data flow
- Category theory wiring diagram style for complex systems
- Apply the scientific method for debugging


## Plausible Property Testing

### Overview
Plausible is Lean 4's property-based testing framework (similar to QuickCheck). It provides rapid counterexample finding to validate specifications before attempting full proofs.

### When to Use Plausible
- **Before writing proofs**: Use `plausible` to quickly check if your spec holds for random inputs
- **Instead of bare `sorry`**: Replace `sorry` with `by plausible; sorry` to catch early mistakes
- **During spec development**: Test edge cases and assumptions as you write specifications
- **For regression testing**: Ensure changes don't break existing properties

### Basic Usage

```lean
-- As a tactic in proofs
theorem my_property : ∀ n : Nat, n + 0 = n := by
  plausible  -- Tests 100 random examples by default
  -- If no counterexample found, continues like admit
  sorry  -- Replace with actual proof later

-- With custom configuration
theorem complex_property : ∀ xs : List Nat, xs.reverse.reverse = xs := by
  plausible (config := { numInst := 500 })  -- Test 500 examples
  sorry

-- For quick checks during development
#eval Plausible.Testable.check <| ∀ xs ys : List Nat, xs ++ ys = ys ++ xs
-- Output: Found counterexample: xs := [0], ys := [1]
```

### Using PlausibleUtils

The `Testing.PlausibleUtils` module provides convenient helpers:

```lean
import Testing.PlausibleUtils

-- Quick tactics
example : ∀ n : Nat, n * 2 = 2 * n := by
  quick_plausible  -- Only 20 tests for speed

-- IO-based testing  
#eval checkWithMsg "My property description" <|
  ∀ n : Nat, n < n + 1

-- Pattern-based helpers
#eval checkForAll (fun n : Nat => n + 0 = n) 100
#eval checkImplication 
  (fun n : Nat => n > 5)  -- precondition
  (fun n : Nat => n > 3)  -- postcondition
  100
```

### Custom Sampleable Instances

For custom types, implement `Sampleable` and `PrintableProp`:

```lean
structure Point where
  x : Int
  y : Int

instance : Sampleable Point where
  sample := do
    let x ← Sampleable.sample (α := Int)
    let y ← Sampleable.sample (α := Int)
    pure { x := x, y := y }

instance : PrintableProp Point where
  printProp p := s!"Point {{ x := {p.x}, y := {p.y} }}"
```

### Best Practices

1. **Start with plausible**: Before writing complex proofs, use plausible to validate assumptions
2. **Incremental testing**: Test smaller properties first, then compose
3. **Document counterexamples**: When plausible finds issues, document them as test cases
4. **Balance test count**: Use fewer tests (20-50) for quick checks, more (100-500) for critical properties
5. **Combine with sorry**: Use `by plausible; sorry` as improved sorry-driven development

### Integration with Spec Development

When developing specifications:
1. Write the spec
2. Add `plausible` tests for edge cases
3. Implement incrementally
4. Use plausible to catch regressions
5. Replace with full proofs when ready

Example workflow:
```lean
def mySpec (impl : Nat → Nat) : Prop :=
  ∀ n, impl n ≥ n

-- Quick validation
example : mySpec (fun n => n + 1) := by
  plausible (config := { numInst := 100 })
  
-- Found issue? Add specific test
example : mySpec (fun n => n - 1) := by
  plausible  -- Will find counterexample: n := 0
```

## Important Lean Documentation Resources

When working with Lean 4, consult these authoritative sources:

- **Lean 4 Official Documentation**: <https://lean-lang.org/lean4/doc> - The formal Lean documentation covering language features, tactics, and standard library
- **Mathlib Manual**: <https://leanprover-community.github.io/mathlib-manual/html-multi/Guides/> - Comprehensive guide to mathlib conventions, tactics, and best practices
- **Lean Language Reference**: <https://lean-lang.org/doc/reference/latest/> - The definitive Lean language reference for syntax and semantics
- **Plausible Testing**: See `Mathlib.Testing.Plausible` for property-based testing documentation



## Development Tools and Workflow


### Version Control

**Jujutsu (jj) Setup for GitHub-friendly Development:**

- Use `jj git init --colocate` for existing git repos (recommended for this project)
- Colocated repos automatically sync jj and git on every command
- Enables mixing `jj` and `git` commands seamlessly
- Tools expecting `.git` directory continue to work

**Essential jj configuration:**

```bash
jj config edit --user
```

Add these settings:

```toml
[git]
auto-local-bookmark = true  # Import all remote bookmarks automatically

[snapshot]  
auto-update-stale = true    # Auto-update stale working copies when switching contexts
```



**Key workflow improvements over git:**

- Anonymous branches - no need to name every small change
- Better conflict resolution and interactive rebase
- `jj absorb` automatically squashes changes into relevant ancestor commits
- `jj undo` and `jj op restore` for powerful history manipulation
- Empty commit on top by default (enables easier experimentation)

**GitHub integration commands:**

- `jj git fetch` + `jj rebase -d main` (replaces `git pull`)
- `jj bookmark create <name>` for named branches
- SSH keys recommended for GitHub (as of Oct 2023)
- Support for both "add commits" and "rewrite commits" review workflows

## Common Lean Pitfalls

- [Automatic implicit parameters](https://github.com/nielsvoss/lean-pitfalls#automatic-implicit-parameters)
- [Forgetting the Mathlib cache](https://github.com/nielsvoss/lean-pitfalls#forgetting-the-mathlib-cache)
- [Using `have` for data](https://github.com/nielsvoss/lean-pitfalls#using-have-for-data)
- [Rewriting under binders](https://github.com/nielsvoss/lean-pitfalls#rewriting-under-binders)
- [Trusting tactics to unfold definitions](https://github.com/nielsvoss/lean-pitfalls#trusting-tactics-to-unfold-definitions)
- [Using `b > a` instead of `a < b`](https://github.com/nielsvoss/lean-pitfalls#using-b--a-instead-of-a--b)
- [Confusing `Prop` and `Bool`](https://github.com/nielsvoss/lean-pitfalls#confusing-prop-and-bool)
- [Not checking for distinctness](https://github.com/nielsvoss/lean-pitfalls#not-checking-for-distinctness)
- [Not accounting for 0](https://github.com/nielsvoss/lean-pitfalls#not-accounting-for-0)
- [Division by 0](https://github.com/nielsvoss/lean-pitfalls#division-by-0)
- [Integer division](https://github.com/nielsvoss/lean-pitfalls#integer-division)
- [Natural number subtraction](https://github.com/nielsvoss/lean-pitfalls#natural-number-subtraction)
- [Other partial functions](https://github.com/nielsvoss/lean-pitfalls#other-partial-functions)
- [Wrapping arithmetic in `Fin`](https://github.com/nielsvoss/lean-pitfalls#wrapping-arithmetic-in-fin)
- [Real power](https://github.com/nielsvoss/lean-pitfalls#real-power)
- [Distance in `Fin n → ℝ`](https://github.com/nielsvoss/lean-pitfalls#distance-in-fin-n-%E2%86%92-%E2%84%9D)
- [Accidental double `iInf` or `iSup`](https://github.com/nielsvoss/lean-pitfalls#accidental-double-iinf-or-isup)
- [Trying to extract data from proofs of propositions](https://github.com/nielsvoss/lean-pitfalls#trying-to-extract-data-from-proofs-of-propositions)
- [Working with equality of types](https://github.com/nielsvoss/lean-pitfalls#working-with-equality-of-types)
- [Parameters for instances that already exist](https://github.com/nielsvoss/lean-pitfalls#parameters-for-instances-that-already-exist)
- [Using `Set`s as types](https://github.com/nielsvoss/lean-pitfalls#using-sets-as-types)
- [Sort _](https://github.com/nielsvoss/lean-pitfalls#sort-_)
- [Trying to prove properties about Float](https://github.com/nielsvoss/lean-pitfalls#trying-to-prove-properties-about-float)
- [`native_decide`](https://github.com/nielsvoss/lean-pitfalls#native_decide)
- [Panic does not abort](https://github.com/nielsvoss/lean-pitfalls#panic-does-not-abort)
- [Lean 3 code](https://github.com/nielsvoss/lean-pitfalls#lean-3-code)
- [Non-terminal simp](https://github.com/nielsvoss/lean-pitfalls#non-terminal-simp)
- [Ignoring warnings](https://github.com/nielsvoss/lean-pitfalls#ignoring-warnings)
- [Ambiguous unicode characters](https://github.com/nielsvoss/lean-pitfalls#ambiguous-unicode-characters)

## misc lean tips

- `#v[..]` is the literal syntax for a `Vector`
- A good default tactic is `try?`