import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_cos {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_cos_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_cos x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.cos (x.get i) ∧
                  result.get i ≥ -1 ∧ result.get i ≤ 1 ∧
                  (x.get i = 0 → result.get i = 1)⌝⦄ := by
  sorry
