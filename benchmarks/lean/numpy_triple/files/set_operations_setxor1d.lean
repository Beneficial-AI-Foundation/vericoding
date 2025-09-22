-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_setxor1d {n m k : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) : Id (Vector Float k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_setxor1d_spec {n m k : Nat} (ar1 : Vector Float n) (ar2 : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_setxor1d ar1 ar2
    ⦃⇓result => ⌜
      -- Result is sorted
      (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
      -- Result has no duplicates
      (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
      -- Every element in result is from exactly one input array
      (∀ i : Fin k, 
        (∃ j : Fin n, ar1.get j = result.get i ∧ ¬∃ l : Fin m, ar2.get l = result.get i) ∨
        (∃ j : Fin m, ar2.get j = result.get i ∧ ¬∃ l : Fin n, ar1.get l = result.get i)) ∧
      -- Every element that appears in exactly one input array is in the result
      (∀ x : Float, 
        ((∃ i : Fin n, ar1.get i = x ∧ ¬∃ j : Fin m, ar2.get j = x) ∨
         (∃ i : Fin m, ar2.get i = x ∧ ¬∃ j : Fin n, ar1.get j = x)) →
        ∃ i : Fin k, result.get i = x)
    ⌝⦄ := by
  sorry
-- </vc-theorems>