import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def asmatrix {n : Nat} (data : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem asmatrix_spec {n : Nat} (data : Vector Float n) :
    ⦃⌜True⌝⦄
    asmatrix data
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = data.get i⌝⦄ := by
  sorry
