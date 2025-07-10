import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Maximum Difference

This module ports the Dafny synthesis task for finding the maximum difference between
any two elements in an array.

The specification includes:
- A method `maxDifference` that returns the maximum difference
- Requires the array to have at least 2 elements
- Ensures the result is the maximum of all possible differences a[i] - a[j]
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisMaxDifference

/-- Implementation placeholder for maxDifference -/
def maxDifference (a : Array Int) : Id Int := sorry

/-- Hoare triple for maxDifference -/
theorem maxDifference_spec (a : Array Int) 
    (h : a.size > 1) :
    ⦃⌜a.size > 1⌝⦄ 
    maxDifference a
    ⦃⇓diff => ⌜∀ i j : Nat, i < a.size → j < a.size → a[i]! - a[j]! ≤ diff⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisMaxDifference