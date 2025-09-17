# VeriCoding Project Overview

**Project Context**: This is a verification-focused coding project across Lean 4, Dafny, and Verus.

Remember that you are run across multiple cycles, so focus on iterating and making incremental progress on a solution rather than getting desperate to one-shot it.

## MCP

- Lean MCP: `uvx lean-lsp-mcp`. You'll need its search capabilities since your training date cutoff is very out of date for Lean 4.

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

- `lean_hover_info`: Retrieve hover information (documentation) for symbols, terms, and expressions in a Lean file (at a specific line & column).

Example output (hover info on a `sorry`):

```text
The `sorry` tactic is a temporary placeholder for an incomplete tactic proof,
closing the main goal using `exact sorry`.

This is intended for stubbing-out incomplete parts of a proof while still having a syntactically correct proof skeleton.
Lean will give a warning whenever a proof uses sorry, so you aren't likely to miss it,
but you can double check if a theorem depends on sorry by looking for sorryAx in the output
of the #print axioms my_thm command, the axiom used by the implementation of sorry.
```

`lean_completions`: Code auto-completion: Find available identifiers or import suggestions at a specific position (line & column) in a Lean file. Use this to fill in program fragments.

#### 6. `lean_multi_attempt`
Try multiple Lean code snippets at a line and return goal state and diagnostics for each.

- `lean_declaration_file`: Get the file contents where a symbol or term is declared. Use this to find the definition of a symbol.

#### 8. Search Tools:
- `lean_leansearch`: Natural language and Lean term search (limit: 3req/30s)
- `lean_loogle`: Search by constant, lemma name, type shape, or conclusion (limit: 3req/30s)
- `lean_state_search`: Search theorems based on proof state (limit: 3req/30s)
- `lean_hammer_premise`: Search premises using Lean Hammer (limit: 3req/30s)

## General Programming Philosophy

Programming is about onomastics (naming), composition (functoriality), and caching. Think conformally (at every scale and across scales).

Build a pit of success: internal systems that grow as a whole outwards, never allowing the fallible external world to leak in except at boundaries. Meet the external world at well-defined interfaces.

When solving problems, write tooling/linters/auto-fixers to widen the pit of success. Use rigid compiler error messages and linter warnings to guide future users (**including** AI) toward correct solutions.

Lean's mut notation is really useful, don't be afraid to use it.

## Project Structure

- `.mcp.json` - MCP server configuration for Lean development tools
- `CLAUDE.md` - This file, containing project instructions and Lean development guidelines
- Additional Lean files and experiments to be created as needed

## Development Commands

For Lean development, the key command is:
- `lake build` (use frequently for constant feedback). It can take filenames as arguments to build them separately.

The lean-lsp-mcp tools are already configured in `.mcp.json` and available through the MCP interface.

## Experiment Tracking

Uses Weights & Biases (wandb) for tracking verification experiments, failure analysis, and LLM usage metrics

## Lean 4 Development Guidelines


- Wrap reserved names in «guillemets» when needed
- Implement "notation typeclasses" like `GetElem`, `Add`, etc where appropriate.
- Practice "sorry-friendly programming": Instead of a comment you put down a spec, but it is only "proved" with `sorry`. If it should compile, use a named hole instead. This is strictly better than a comment, because the typechecker will use it for program generation.
- Decompose proofs until tools like `canonical`, `grind`, and `simp` dissolve the pieces. Use them to do the "how", the AI should do the "what".
- Don't use `i` and `j` as variable names when you could use `r`(ow) and `c`(olumn) instead. Ditto for `m` and `n` as matrix dimensions. Use `R` and `C`.
### Import and Module Structure

- Imports MUST come before any syntax elements, including module and doc comments
  - [ ] TODO set extensible error messages to suggest a fix for AI. Then remove this admonishment.
- Set `linter.missingDocs = true` and `relaxedAutoImplicit = false` in `lakefile.lean`.

### Common Errors and Solutions

- **"unexpected token 'namespace'"**: Module/doc comment placed incorrectly (should be after imports)
- **"unexpected token"**: Often caused by misplaced docstrings - use multiline comments instead
  - [ ] use extensible error messages to suggest a fix for AI. Then remove this admonishment.

## Python Development Guidelines

- Always use `uv` for Python package management (not pip). Use `uv add` over `uv pip install`, `uv sync`, and `uv run` over `python`.

## Additional Guidelines

- Use `rg` and `fd` instead of grep/find. Search in `.lake` for the source code, it's a reliable way to find source of truth.


## Development Strategies

### Lean 4 Development Approach

- Read the reference manual assiduously. Ultrathink.
- Spam `lake build` to verify the pieces work and build up FUNCTORIALLY.
- Use compiler tooling like extensible error messages, `grind`, `simproc` (pattern guided reductions), and metaprogramming to build a pit of success.
- If you solve a hard problem, write down what you did somehow.
- Try harder to index without `!` or `?` - name `match`/`if` branches for better inference

```lean
example := if h : 2 = 2 then 3 else 4 -- names `h` as `Prop` that `2 = 2`
```

- Raw string syntax: `r#".."#`, multiline strings use `\` continuation
- Use `lakefile.lean` over `lakefile.toml` for better AI introspection and metaprogramming
- Incorporate positive surprises into memories - stay curious!

### Debugging and Development Process

- Use named holes like `?holeName` for well-typed fragment programs. Use meaningful names for the holes.
- Make mermaid diagrams with labeled edges describing data flow
- Category theory wiring diagram style for complex systems
- Apply the scientific method for debugging

## Important Lean Documentation Resources

When working with Lean 4, consult these authoritative sources:

- **Lean Language Reference**: <https://lean-lang.org/doc/reference/latest/> - The definitive Lean language reference for syntax and semantics

- **Mathlib Manual**: <https://leanprover-community.github.io/mathlib-manual/html-multi/Guides/> - Comprehensive guide to mathlib conventions, tactics, and best practices.



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
- For Numpy-like functions, use `Vector a n` as the base type, it's in prelude.
- `mathlib` is full of noncomputable code. Avoid using its data structures, only its theorems.

## sorry vs named holes

Named holes are better than `sorry` because they dump the *local context*.

```lean
/--
don't know how to synthesize placeholder
context:
case probablyZero
someCtx : Nat := 2
⊢ Nat
-/
def a : Nat :=
  let someCtx := 2
  let probablyZero := ?probablyZero
  ?probablyZero -- uses the hole in 2 places

/--
declaration uses 'sorry'
-/
def a' : Nat :=
  let someCtx := 2
  sorry

-- Underscores aren't as good as named holes because they elide actual values
/--
don't know how to synthesize placeholder
context:
someCtx : Nat := ⋯
⊢ Nat
-/
def a'' : Nat :=
  let someCtx := 2
  _
```


## Tips for working across iterations

Use named holes as Schelling points for agents to coordinate across iterations. Good names help other agents fill in the holes.

You can use guillemets with holes to create "natural language" holes.

```lean
/--
don't know how to synthesize placeholder
context:
someCtx : Nat := ⋯
⊢ Nat
-/
def a'' : Nat :=
  let someCtx := 2
  ?«a whole sentence»
```

## Tactic coding

### `grind`

`grind` is Lean's new equivalent of a hammer. See <https://lean-lang.org/doc/reference/latest/The--grind--tactic> for how to configure it. It takes some steps, but it's worth it. `unfold` + `grind` should be a good starting point for proofs.

`grind` is on par with `simp`.
