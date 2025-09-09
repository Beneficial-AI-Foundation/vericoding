import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def fromiter {α : Type} (n : Nat) (iter : Fin n → α) : Id (Vector α n) :=
  sorry

theorem fromiter_spec {α : Type} (n : Nat) (iter : Fin n → α) :
    ⦃⌜True⌝⦄
    fromiter n iter
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = iter i⌝⦄ := by
  sorry
