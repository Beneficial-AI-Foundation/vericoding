-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_square {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_square_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_square x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (x.get i) * (x.get i) ∧ 
                 result.get i ≥ 0⌝⦄ := by
  sorry
-- </vc-theorems>