# Weak Specification Reports

This document lists all inspection samples where the specification was classified as **[Weak]** - specs with omissions leading to easier or trivial problems.

## Summary

| Language | Count |
|----------|-------|
| Dafny | 3 |
| Lean | 4 |
| Verus | 7 |
| **Total** | **14** |

---

## Dafny

### DA0355 - apps
- **File:** `152_apps_test_1836_impl_grok-code.dfy`
- **LLM:** grok-code
- **Issue:** Unmodified. However, the specification permits a trivial solution, likely unintended.

### DA0454 - apps
- **File:** `248_apps_test_2594_impl_claude-sonnet.dfy`
- **LLM:** claude-sonnet
- **Issue:** Does not define a solve method, assume {:axiom} false is just a floating code block.

### DT0202 - numpy_triple
- **File:** `131_io_operations_array_str_impl_gemini.dfy`
- **LLM:** gemini
- **Issue:** ArrayStr spec is weak: only ensures non-empty result, bracket structure, and a vague ordering property (exists pos_i, pos_j for elements). Does not actually specify that the string representation is correct (i.e., contains the actual values). Original Lean problem also missing this last constraint.

---

## Lean

### LD0383 - dafnybench
- **File:** `dafny-synthesis_task_id_770_SumOfFourthPowerOfOddNumbers_impl_gpt.lean`
- **LLM:** gpt-5
- **Issue:** Arguably the original spec is weak, wants a loop to calculate rather than the algebra.

### LV0140 - verina
- **File:** `verina_basic_60_task_impl_gpt-mini.lean`
- **LLM:** gpt-5-mini
- **Issue:** Spec clearly intended something different according to definition name. Problem present in the original.

### LC0045 - humaneval
- **File:** `HumanEval_46_impl_gpt.lean`
- **LLM:** gpt-5
- **Issue:** NL spec says "write a function to efficiently compute the n-th element of the fib4 number sequence. Do not use recursion." but spec theorem does not require this.

### LA0402 - appstest
- **File:** `apps_test_2209_impl_claude-sonnet.lean`
- **LLM:** claude-sonnet-4
- **Issue:** Maybe there should be additional parts of the spec given the many introduced functions. Original Dafny problem has same issue.

---

## Verus

### VT0083 - numpy_triple
- **File:** `51_constants_NPY_SQRT1_2_impl_gpt-mini.rs`
- **LLM:** gpt-mini
- **Issue:** Does not have any ensures clause whatsoever.

### VT0250 - numpy_triple
- **File:** `108_mathematical_functions_around_impl_gpt.rs`
- **LLM:** gpt
- **Issue:** Inserts requires statement instead of default value. Original spec does not ensure that entry is rounded to required decimal precision. Admits trivial solution.

### VS0024 - numpy_simple
- **File:** `VS0024_NpHistogram_impl_claude-opus-4.1.rs`
- **LLM:** claude-opus-4.1
- **Issue:** Helper and main function not adequately separated in original problem.

### VS0040 - numpy_simple
- **File:** `VS0040_NpPolyder_impl_claude-opus-4.1.rs`
- **LLM:** claude-opus-4.1
- **Issue:** Original spec is weak. Any vector of acceptable length satisfies the spec.

### VV0005 - verina
- **File:** `23_verina_advanced_9_task_impl_gpt.rs`
- **LLM:** gpt
- **Issue:** Loses constraints during transpilation.

### VA0306 - apps
- **File:** `apps_test_1576.rs`
- **LLM:** claude-opus-4.1
- **Issue:** Types narrowed (string -> Vec<char>). However, the original Dafny spec is trivially satisfiable: it specifies that output length equals input length without any notion of decryption.

### VA0514 - apps
- **File:** `apps_test_4261.rs`
- **LLM:** claude-sonnet-4
- **Issue:** Postconditions lost in transpilation. Types narrowed (string -> Vec<i8>). The Dafny spec requires parsing 3 space-separated integers and ensures output == IntToString(RemainingWater(a,b,c)) + newline. The Verus spec only has requires input.len() > 0 with no ensures whatsoever. Preamble functions (valid_input, remaining_water) are present but unused in the spec.
