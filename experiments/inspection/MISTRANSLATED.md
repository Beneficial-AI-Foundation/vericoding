# Mistranslated Specification Reports

This document lists all inspection samples where the specification was classified as **[Mistranslated]** - type changes or semantic differences from the original spec.

## Summary

| Language | Count |
|----------|-------|
| Dafny | 3 |
| Lean | 0 |
| Verus | 4 |
| **Total** | **7** |

---

## Dafny

### DV0117 - verina
- **File:** `102_verina_basic_66_task_impl_grok-code.dfy`
- **LLM:** grok-code
- **Issue:** The postcondition `exists k, x = 2 * k` from Lean turned into `x % 2 == 0` in the Dafny spec, trivializing the solution.

### DS0024 - numpy_simple
- **File:** `20_NpHistogram-spec_impl_gemini-flash.dfy`
- **LLM:** gemini-flash
- **Issue:** histogram_helper has weak spec - only ensures result length, not actual histogram correctness. The main histogram method uses assume {:axiom} false which means it is not actually verified. The original Lean problem actually asks for implementations for both the histogram and histogram_helper. The translation should have asked for the histogram method without the histogram_helper. The spec does not relate bin boundaries to count values. The original Lean problem requires the bin boundaries to be totally ordered, but does not ensure that the values are correctly counted.

### DS0048 - numpy_simple
- **File:** `38_NpShape-spec_impl_deepseek.dfy`
- **LLM:** deepseek
- **Issue:** The original Lean problem actually has two different subproblems, one for ShapeArrays and one for Matrix. The translation picked the Matrix subproblem as the main problem. The Matrix object in the original Lean problem is defined as a map from Fin m and Fin n to the entry type α. But in the translation, the Matrix datatype stores m, n separately from data without consistency check. ShapeArrays is marked {:axiom} (unverified). ShapeMatrix spec is straightforward - returns [m, n] for a Matrix, but is incorrectly marked {:axiom} (unverified).

---

## Lean

*No mistranslated specifications found in Lean samples.*

---

## Verus

### VB0060 - bignum
- **File:** `8_bignums_Sub_NormalizeBitstring_impl_claude-sonnet.rs`
- **LLM:** claude-sonnet
- **Issue:** Superimposes spec function and preamble function.

### VB0060 - bignum (duplicate entry)
- **File:** `8_bignums_Sub_NormalizeBitstring_impl_claude-opus.rs`
- **LLM:** claude-opus
- **Issue:** Superimposes spec function and preamble function. Same underlying file as above.

### VT0273 - numpy_triple
- **File:** `115_mathematical_functions_floor_impl_gemini-flash.rs`
- **LLM:** gemini-flash
- **Issue:** Floats change to i32 in transpilation.

### VD0080 - dafnybench
- **File:** `Clover_return_seven_M.rs`
- **LLM:** gemini-2.5-flash
- **Issue:** The transpiled spec uses `fn M(x: int)` but `int` is a ghost type in Verus, making this invalid for an exec function. The LLM changed it to `proof fn M(x: int)` to make it compile. This modifies the function kind (exec -> proof) but preserves the ensures clause `seven == 7`.

---

## Common Patterns

### Type Changes
- **Float → i32** (VT0273): Floating-point semantics lost
- **int → ghost type issue** (VD0080): Verus's `int` is ghost-only, requiring function kind change

### Structural Changes
- **Function merging** (VB0060): Spec and preamble functions incorrectly combined
- **Subproblem selection** (DS0048): Wrong subproblem chosen from multi-part original
- **Logical simplification** (DV0117): `∃ k, x = 2*k` → `x % 2 == 0` (semantically similar but structurally different)
