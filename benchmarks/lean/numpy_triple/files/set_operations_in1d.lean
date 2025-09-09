import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def in1d {α : Type} {m n : Nat} [DecidableEq α] (ar1 : Vector α m) (ar2 : Vector α n) : Id (Vector Bool m) :=
  sorry

theorem in1d_spec {α : Type} {m n : Nat} [DecidableEq α] (ar1 : Vector α m) (ar2 : Vector α n) :
    ⦃⌜True⌝⦄
    in1d ar1 ar2
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = true ↔ ∃ j : Fin n, ar1.get i = ar2.get j⌝⦄ := by
  sorry
