import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def shape {α : Type} {n : Nat} (a : Vector α n) : Id Nat :=
  sorry

theorem shape_spec {α : Type} {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    shape a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  sorry
