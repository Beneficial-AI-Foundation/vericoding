-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def signbit {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem signbit_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    signbit x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (x.get i < 0)⌝⦄ := by
  sorry
-- </vc-theorems>