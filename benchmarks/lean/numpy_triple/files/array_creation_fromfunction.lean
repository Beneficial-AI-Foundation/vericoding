import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def fromfunction {n : Nat} (f : Fin n → Float) : Id (Vector Float n) :=
  sorry

theorem fromfunction_spec {n : Nat} (f : Fin n → Float) :
    ⦃⌜True⌝⦄
    fromfunction f
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = f i⌝⦄ := by
  sorry
