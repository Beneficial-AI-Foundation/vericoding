-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique {n : Nat} (arr : Vector Int n) : Id (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_spec {n : Nat} (arr : Vector Int n) :
    ⦃⌜True⌝⦄
    unique arr
    ⦃⇓result => ⌜(∀ i j : Nat, i < j → j < result.length → result[i]? < result[j]?) ∧ 
                  (∀ i : Nat, i < result.length → ∃ j : Fin n, result[i]? = some (arr.get j)) ∧
                  (∀ i j : Nat, i < result.length → j < result.length → i ≠ j → result[i]? ≠ result[j]?) ∧
                  (∀ i : Fin n, ∃ j : Nat, j < result.length ∧ some (arr.get i) = result[j]?)⌝⦄ := by
  sorry
-- </vc-theorems>