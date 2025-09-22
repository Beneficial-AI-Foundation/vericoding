-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanargmax {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) : Id (Fin (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanargmax_spec {n : Nat} (a : Vector Float (n + 1)) (h_not_all_nan : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) :
    ⦃⌜∃ i : Fin (n + 1), ¬(a.get i).isNaN⌝⦄
    nanargmax a h_not_all_nan
    ⦃⇓idx => ⌜¬(a.get idx).isNaN ∧ 
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j ≤ a.get idx) ∧
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get j = a.get idx → idx ≤ j)⌝⦄ := by
  sorry
-- </vc-theorems>