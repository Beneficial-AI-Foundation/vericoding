-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanargmin {n : Nat} (a : Vector Float (n + 1)) (h_has_valid : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) : Id (Fin (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nanargmin_spec {n : Nat} (a : Vector Float (n + 1)) (h_has_valid : ∃ i : Fin (n + 1), ¬(a.get i).isNaN) :
    ⦃⌜∃ i : Fin (n + 1), ¬(a.get i).isNaN⌝⦄
    nanargmin a h_has_valid
    ⦃⇓idx => ⌜¬(a.get idx).isNaN ∧ 
             (∀ j : Fin (n + 1), ¬(a.get j).isNaN → a.get idx ≤ a.get j) ∧
             (∀ j : Fin (n + 1), j < idx → (a.get j).isNaN ∨ a.get j > a.get idx)⌝⦄ := by
  sorry
-- </vc-theorems>