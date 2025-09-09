import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_flat {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_flat_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_flat a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get i⌝⦄ := by
  sorry
