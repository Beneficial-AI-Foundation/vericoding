import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ones (n : Nat) : Id (Vector Float n) :=
  sorry

theorem ones_spec (n : Nat) :
    ⦃⌜True⌝⦄
    ones n
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = 1.0) ∧ 
                 (∀ i j : Fin n, result.get i = result.get j) ∧
                 (∀ i : Fin n, result.get i > 0) ∧
                 (∀ i : Fin n, ∀ x : Float, x * result.get i = x)⌝⦄ := by
  sorry
