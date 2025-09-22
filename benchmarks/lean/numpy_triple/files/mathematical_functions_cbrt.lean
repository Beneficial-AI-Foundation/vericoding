-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cbrt {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cbrt_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    cbrt x
    ⦃⇓result => ⌜∀ i : Fin n, (result.get i) ^ 3 = x.get i⌝⦄ := by
  sorry
-- </vc-theorems>