import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def asanyarray {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem asanyarray_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    asanyarray a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get i⌝⦄ := by
  sorry
