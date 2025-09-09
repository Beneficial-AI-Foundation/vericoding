import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def logical_not {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry

theorem logical_not_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    logical_not x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (x.get i = 0.0)⌝⦄ := by
  sorry
