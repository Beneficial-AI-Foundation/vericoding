import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ravel {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem ravel_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    ravel a
    ⦃⇓result => ⌜result = a⌝⦄ := by
  sorry
