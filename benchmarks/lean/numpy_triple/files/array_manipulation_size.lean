import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def size {n : Nat} (a : Vector Float n) : Id Nat :=
  sorry

theorem size_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    size a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  sorry
