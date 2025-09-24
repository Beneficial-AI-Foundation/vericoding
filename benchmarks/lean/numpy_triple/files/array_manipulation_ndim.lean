-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ndim {α : Type} {n : Nat} (a : Vector α n) : Id Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ndim_spec {α : Type} {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    ndim a
    ⦃⇓result => ⌜result = 1⌝⦄ := by
  sorry
-- </vc-theorems>