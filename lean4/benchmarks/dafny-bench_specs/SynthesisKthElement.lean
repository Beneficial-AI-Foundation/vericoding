import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Synthesis Task: Kth Element

This module ports the Dafny synthesis task for accessing the k-th element of an array.

The specification includes:
- A method `kthElement` that returns the element at position k (1-indexed)
- Requires k to be between 1 and the array length
- Ensures the result is the element at index k-1 (0-indexed)
-/

namespace NumpySpec.DafnyBenchmarks.SynthesisKthElement

/-- Implementation placeholder for kthElement -/
def kthElement (arr : Array Int) (k : Int) : Id Int := sorry

/-- Hoare triple for kthElement -/
theorem kthElement_spec (arr : Array Int) (k : Int) 
    (h : 1 ≤ k ∧ k ≤ arr.size) :
    ⦃⌜1 ≤ k ∧ k ≤ arr.size⌝⦄ 
    kthElement arr k
    ⦃⇓result => ⌜result = arr[(k - 1).toNat]!⌝⦄ := by
  sorry

end NumpySpec.DafnyBenchmarks.SynthesisKthElement