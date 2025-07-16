# DafnyBenchmarks - Ported Specifications

This directory contains Lean 4 ports of Dafny specifications from the vericoding project.

## Successfully Ported Specifications

The following specifications have been successfully ported and compile:

1. **EvenList.lean** - Extracts all even numbers from an array while preserving order
2. **HasCloseElements.lean** - Checks if any two distinct elements are closer than a threshold
3. **IsEven.lean** - Simple predicate to check if an integer is even
4. **IsPalindrome.lean** - Checks if a character sequence reads the same forwards and backwards

## Specifications with Compilation Issues

The following specifications have been ported but have remaining compilation issues that need to be resolved:

5. **Find.lean** - Linear search returning index or -1
   - Issue: Type mismatch with negative numbers in the specification
6. **Insert.lean** - Inserts characters from one array into another
   - Issue: Complex let-binding syntax in Id monad
7. **IntegerSquareRoot.lean** - Computes integer square root
   - Issue: Termination proof needed for recursive function
8. **LinearSearch1.lean** - Linear search returning index or array size
   - Issue: Specification proof obligations
9. **LinearSearch2.lean** - Linear search with precondition that element exists
   - Issue: Handling panic in specification
10. **LinearSearch3.lean** - Generic linear search with predicate
    - Issue: Handling panic in specification with generic types

## Porting Approach

Each specification follows the Hoare triple style using the `Std.Do.Triple` library:
- `⦃⌜precondition⌝⦄ program ⦃⇓result => ⌜postcondition⌝⦄`
- All proofs are currently marked with `sorry` and need to be completed
- The `mvcgen` tactic is used for generating verification conditions

## Next Steps

1. Fix the remaining compilation issues in files 5-10
2. Complete the proofs (replace `sorry` with actual proofs)
3. Add property-based tests using the Plausible library
4. Benchmark the implementations