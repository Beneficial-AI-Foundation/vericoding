-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lagweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lagweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    lagweight x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (-x.get i)⌝⦄ := by
  sorry
-- </vc-theorems>