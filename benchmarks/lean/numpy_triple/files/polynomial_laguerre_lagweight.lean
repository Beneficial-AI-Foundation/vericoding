import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def lagweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem lagweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    lagweight x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (-x.get i)⌝⦄ := by
  sorry
