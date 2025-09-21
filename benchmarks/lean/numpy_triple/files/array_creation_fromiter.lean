-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromiter {α : Type} (n : Nat) (iter : Fin n → α) : Id (Vector α n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromiter_spec {α : Type} (n : Nat) (iter : Fin n → α) :
    ⦃⌜True⌝⦄
    fromiter n iter
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = iter i⌝⦄ := by
  sorry
-- </vc-theorems>