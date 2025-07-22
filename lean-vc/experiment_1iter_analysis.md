# Lean Spec-to-Code Experiment: 1-Iteration Results Analysis

## Executive Summary

- **Total specs tested**: 50
- **Success rate**: 1/50 (2%)
- **Actual success rate**: 0/50 (0%) - the single "success" was a file without any `sorry` placeholders

## Results Breakdown

### The Single "Success": Numpy_Stack.lean

Upon investigation, `Numpy_Stack.lean` doesn't contain any actual implementation task. It's a documentation file explaining why stack operations are out of scope for 1D-only implementations. The LLM correctly returned the file unchanged, which passed verification trivially.

### Failure Analysis (49 files)

#### Most Common Error Categories

1. **Unknown Constants/Identifiers (60% of failures)**
   - `unknown constant 'Id.pure'` - appears in 12+ files
   - `unknown identifier 'Vector.get_zipWith'`
   - `unknown identifier 'Std.Do.hoareTriple_returnPure'`
   - `unknown identifier 'htb_of_pure'`
   - Various other missing Hoare triple identifiers

2. **Tactic Failures (25% of failures)**
   - `tactic 'constructor' failed, target is not an inductive datatype` - appears in 8+ files
   - `tactic 'rfl' failed` - type mismatches in proofs
   - `unsolved goals` - incomplete proofs
   - `simp made no progress` - simplification tactics failing

3. **Syntax Errors (10% of failures)**
   - `unexpected token ':'; expected '}'` - struct syntax issues
   - Invalid constructor syntax
   - Incorrect function application syntax

4. **Type System Issues (5% of failures)**
   - `Application type mismatch`
   - `failed to synthesize Decidable`
   - Constructor argument count mismatches

### Specific Examples

1. **Simple Operations That Failed**:
   - `Numpy_Add.lean`: Unknown `Id.pure` and Hoare triple identifiers
   - `Numpy_Multiply.lean`: Struct syntax errors and missing vector operations
   - `zeros.lean`: Unknown constants and type mismatches
   - `ones.lean`: Deprecated API usage and constructor issues

2. **Complex Operations That Failed**:
   - `Numpy_Sort.lean`: Termination proof failure for recursive merge sort
   - `Numpy_Dot.lean`: Proof tactic failure for Hoare triple
   - `Numpy_Matmul.lean`: Multiple unknown identifiers
   - `Numpy_Argsort.lean`: Type mismatch in indexing operations

### Key Insights

1. **Library Knowledge Gap**: The LLM consistently uses identifiers that don't exist in the current Lean 4 environment, suggesting training on different or outdated Lean versions.

2. **Hoare Triple Syntax**: The specific Hoare triple notation used in this project (`⦃P⦄ f ⦃⇓r => Q⦄`) is not well understood by the LLM.

3. **Import Management**: The LLM rarely adds necessary imports, leading to missing identifiers.

4. **Proof Generation**: Even for simple properties, the LLM struggles to generate correct proof tactics.

5. **No Learning Within Single Iteration**: With only 1 iteration, the LLM cannot learn from compiler feedback to fix issues.

## Predictions for 5-Iteration Experiment

Based on these patterns:
- Expected success rate: 10-20% (5-10 files)
- Most likely to succeed: Operations with simple type signatures and minimal proof obligations
- Iterative refinement should help with:
  - Syntax errors
  - Missing imports (if LLM recognizes the pattern)
  - Simple type mismatches
- Unlikely to be fixed even with iterations:
  - Fundamental misunderstanding of Hoare triple syntax
  - Complex termination proofs
  - Deep type system issues

## Conclusion

The 1-iteration experiment demonstrates that current LLMs have significant challenges with formal verification in Lean 4:
- Lack of familiarity with specific project conventions
- Inability to navigate Lean's type system without feedback
- Missing knowledge of current Lean 4 standard library

The iterative refinement in the 5-iteration experiment will be crucial for any meaningful success rate.