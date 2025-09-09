import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def log1p {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem log1p_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > -1⌝⦄
    log1p x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (1 + x.get i) ∧
                   (x.get i = 0 → result.get i = 0) ∧
                   (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
  sorry
