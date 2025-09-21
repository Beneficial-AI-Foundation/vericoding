-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def intersect1d {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) : Id (Vector Int k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem intersect1d_spec {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) :
    ⦃⌜True⌝⦄
    intersect1d ar1 ar2
    ⦃⇓result => ⌜
      -- Result contains only values that exist in both arrays
      (∀ i : Fin k, ∃ j : Fin n, ∃ l : Fin m, 
        result.get i = ar1.get j ∧ result.get i = ar2.get l) ∧
      -- Result is sorted in ascending order
      (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
      -- Result contains unique values (no duplicates)
      (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
      -- Result is complete (contains all common values)
      (∀ val : Int, (∃ i : Fin n, ar1.get i = val) ∧ (∃ j : Fin m, ar2.get j = val) →
        ∃ l : Fin k, result.get l = val)
    ⌝⦄ := by
  sorry
-- </vc-theorems>