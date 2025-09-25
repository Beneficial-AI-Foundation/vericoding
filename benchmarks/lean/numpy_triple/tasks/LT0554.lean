-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def union1d {n m : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) : Id (Vector Float (n + m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem union1d_spec {n m : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) :
    ⦃⌜True⌝⦄
    union1d ar1 ar2
    ⦃⇓result => ⌜
      -- Union property: every element from either input array is in result
      (∀ i : Fin n, ∃ j : Fin (n + m), result.get j = ar1.get i) ∧
      (∀ i : Fin m, ∃ j : Fin (n + m), result.get j = ar2.get i) ∧
      -- Completeness: every element in result comes from one of the input arrays
      (∀ j : Fin (n + m), 
        (∃ i : Fin n, result.get j = ar1.get i) ∨ 
        (∃ i : Fin m, result.get j = ar2.get i)) ∧
      -- Sorted property: result is sorted in ascending order
      (∀ i j : Fin (n + m), i < j → result.get i ≤ result.get j) ∧
      -- Uniqueness property: no duplicate elements
      (∀ i j : Fin (n + m), i ≠ j → result.get i ≠ result.get j)
    ⌝⦄ := by
  sorry
-- </vc-theorems>