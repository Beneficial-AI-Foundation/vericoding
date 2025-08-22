import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.flatnonzero: Return indices that are non-zero in the flattened version of a.

    This function returns the indices of all non-zero elements in the array.
    The returned indices correspond to positions in the flattened array where
    the elements are non-zero.

    For example, if array is [1, 0, 3, 0, 5], the function returns [0, 2, 4]
    indicating that elements at positions 0, 2, and 4 are non-zero.
-/
def flatnonzero {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry

/-- Specification: flatnonzero returns indices of all non-zero elements.

    Precondition: True (no restrictions on input array)
    Postcondition: 
    1. All returned indices correspond to non-zero elements in the original array
    2. All non-zero elements in the original array have their indices in the result
    3. The result contains no duplicate indices
    4. The result indices are sorted in ascending order
-/
theorem flatnonzero_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    flatnonzero a
    ⦃⇓result => ⌜
      -- All indices in result point to non-zero elements
      (∀ i ∈ result, a.get i ≠ 0) ∧
      -- All non-zero elements have their indices in result
      (∀ j : Fin n, a.get j ≠ 0 → j ∈ result) ∧
      -- Result contains no duplicate indices
      (result.Nodup) ∧
      -- Result indices are sorted in ascending order
      (∀ i j : Fin n, i ∈ result → j ∈ result → i < j → 
        result.idxOf i < result.idxOf j)
    ⌝⦄ := by
  sorry
