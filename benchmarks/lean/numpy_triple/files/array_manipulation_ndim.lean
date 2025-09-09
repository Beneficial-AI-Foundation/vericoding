import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ndim {α : Type} {n : Nat} (a : Vector α n) : Id Nat :=
  sorry

theorem ndim_spec {α : Type} {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    ndim a
    ⦃⇓result => ⌜result = 1⌝⦄ := by
  sorry
