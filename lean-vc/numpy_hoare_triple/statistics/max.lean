import Std.Do.Triple
import Std.Tactic.Do
import numpy_hoare_triple.statistics.amax

/-!
{
  "name": "numpy.max",
  "category": "Order statistics",
  "description": "Alias for numpy.amax - Return the maximum of an array or maximum along an axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.max.html",
  "doc": "numpy.max is an alias for numpy.amax. See numpy.amax for full documentation.",
  "code": "# Alias for amax\nmax = amax"
}
-/

open Std.Do

namespace numpy_hoare_triple.statistics

/-- Returns the maximum value of all elements in a non-empty vector.
    This is an alias for numpy.amax that returns the maximum value among all elements in the array.
    
    Mathematical Properties:
    - Returns an element that exists in the vector
    - No element in the vector is greater than the returned value
    - For constant vectors, returns the constant value
    - Handles non-empty vectors only (n + 1 elements) -/
def max {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  amax a

/-- Specification: max returns the maximum value in the vector.
    This specification delegates to amax_spec since max is an alias for amax.
    
    Mathematical properties:
    1. The result is an element that exists in the vector
    2. No element in the vector is greater than the result
    3. The result is unique (first occurrence if there are duplicates)
    4. For constant vectors, max equals the constant value
    5. Sanity check: the maximum exists in the vector -/
theorem max_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    max a
    ⦃⇓result => ⌜-- Core property: result is the maximum element in the vector
                 (∃ max_idx : Fin (n + 1),
                   result = a.get max_idx ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- Uniqueness: result is the first occurrence of the maximum
                 (∃ first_max_idx : Fin (n + 1),
                   result = a.get first_max_idx ∧
                   (∀ i : Fin (n + 1), a.get i = result → first_max_idx ≤ i) ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- For constant vectors, max equals the constant
                 ((∀ i j : Fin (n + 1), a.get i = a.get j) → 
                   result = a.get ⟨0, Nat.zero_lt_succ n⟩) ∧
                 -- Sanity check: the maximum exists in the vector
                 (∃ witness : Fin (n + 1), result = a.get witness)⌝⦄ := by
  -- Since max is defined as amax, we can use amax_spec
  unfold max
  exact amax_spec a

end numpy_hoare_triple.statistics