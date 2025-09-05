/-  numpy.nonzero: Return the indices of the elements that are non-zero.

    Returns a vector of indices where the corresponding elements in the input
    array are non-zero. The indices are returned in row-major, C-style order.

    For a 1D array, this returns a vector containing all indices i such that
    a[i] ≠ 0. Since the output size depends on the input values, we use
    a List structure to accommodate the dynamic nature of the result.

    Note: In the full NumPy implementation, this returns a tuple of arrays
    (one for each dimension), but for 1D arrays we simplify to a single list.
-/

/-  Specification: numpy.nonzero returns indices of all non-zero elements.

    Precondition: True (no constraints on input)
    Postcondition: 
    1. Every index in the result corresponds to a non-zero element in the input
    2. Every non-zero element in the input has its index in the result (completeness)
    3. The indices are in ascending order (preserving array order)
    4. No duplicates in the result
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def nonzero {n : Nat} (a : Vector Float n) : Id (List (Fin n)) :=
  sorry

theorem nonzero_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nonzero a
    ⦃⇓indices => ⌜(∀ i ∈ indices, a.get i ≠ 0) ∧
                   (∀ j : Fin n, a.get j ≠ 0 → j ∈ indices) ∧
                   (∀ i₁ i₂ : Fin n, i₁ ∈ indices → i₂ ∈ indices → i₁ < i₂ → 
                    (indices.idxOf i₁ < indices.idxOf i₂)) ∧
                   (indices.Nodup)⌝⦄ := by
  sorry
