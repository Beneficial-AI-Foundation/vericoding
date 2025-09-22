-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def size {n : Nat} (a : Vector Float n) : Id Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem size_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    size a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  sorry
-- </vc-theorems>