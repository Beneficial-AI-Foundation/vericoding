# DafnyBenchmarks: Porting Dafny Specifications to Lean 4

## Overview

This directory contains Lean 4 ports of Dafny benchmark specifications from the vericoding repository. The goal is to translate Dafny method specifications (preconditions and postconditions) into Lean 4 using Hoare triple notation.


## Porting Methodology

### 1. Specification Style

Each Dafny specification is ported using the Hoare triple style from `Std.Do.Triple`:

```lean
theorem spec_name {params} :
    ⦃⌜precondition⌝⦄
    function_call
    ⦃⇓result => ⌜postcondition⌝⦄ := by
  sorry
```

`function_call` is required to be in a monadic context. Currently, some functions use `Id` but here's an alternative:

```lean
def helper : Int :=
  sorry

theorem spec_name {params} :
    ⦃⌜precondition⌝⦄
    (pure function_call : Id _)
    ⦃⇓result => ⌜postcondition⌝⦄ := by
  sorry
```

## Implementation Notes

1. **Specifications Only**: These files contain only specifications (function signatures and theorem statements), not implementations. All function bodies are minimal placeholders that type-check, and all proofs are `sorry`. This follows the approach where specifications come first, and implementations can be filled in later.

2. **Proof Obligations**: All proofs are currently marked as `sorry`.

## Contributing

When adding new specifications:

1. Follow the existing naming and style conventions
2. Document any deviations from the Dafny original
3. Ensure the file compiles with `lake build $FILENAME`

## Porting Notes

- Use `Rat` over `Float` when division is needed. Else use `Int`. `Float` has poor proving support.

```lean
-- needed at the top of a file for `Rat`s to be in scope
import Std.Internal.Rat
open Std.Internal
```