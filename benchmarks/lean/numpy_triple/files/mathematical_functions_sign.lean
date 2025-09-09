import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def sign {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem sign_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    sign x
    ⦃⇓result => ⌜∀ i : Fin n, 
      (x.get i < 0 → result.get i = -1) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (x.get i > 0 → result.get i = 1)⌝⦄ := by
  sorry
