-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromfunction {n : Nat} (f : Fin n → Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromfunction_spec {n : Nat} (f : Fin n → Float) :
    ⦃⌜True⌝⦄
    fromfunction f
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = f i⌝⦄ := by
  sorry
-- </vc-theorems>