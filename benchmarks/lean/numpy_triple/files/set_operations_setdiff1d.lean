-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def setdiff1d {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) : Id (Vector Int k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem setdiff1d_spec {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) :
    ⦃⌜True⌝⦄
    setdiff1d ar1 ar2
    ⦃⇓result => ⌜-- Each element in result is from ar1 and not in ar2
                 (∀ i : Fin k, ∃ j : Fin n, result.get i = ar1.get j ∧ 
                  ∀ l : Fin m, result.get i ≠ ar2.get l) ∧
                 -- No duplicates in result
                 (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
                 -- Result is sorted
                 (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
                 -- All unique values from ar1 not in ar2 are included
                 (∀ val : Int, (∃ i : Fin n, ar1.get i = val ∧ ∀ j : Fin m, ar2.get j ≠ val) →
                  ∃ i : Fin k, result.get i = val)⌝⦄ := by
  sorry
-- </vc-theorems>