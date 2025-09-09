import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def reshape {n m : Nat} (a : Vector Float n) (h_size : n = m) : Id (Vector Float m) :=
  sorry

theorem reshape_spec {n m : Nat} (a : Vector Float n) (h_size : n = m) :
    ⦃⌜n = m⌝⦄
    reshape a h_size
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = a.get (i.cast h_size.symm)⌝⦄ := by
  sorry
