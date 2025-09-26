-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_reciprocal {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_reciprocal_spec {n : Nat} (x : Vector Float n) 
    (h_nonzero : ∀ i : Fin n, x.get i ≠ 0) :
    ⦃⌜∀ i : Fin n, x.get i ≠ 0⌝⦄
    numpy_reciprocal x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1 / x.get i ∧ 
                 result.get i ≠ 0 ∧
                 (x.get i > 0 → result.get i > 0) ∧
                 (x.get i < 0 → result.get i < 0)⌝⦄ := by
  sorry
-- </vc-theorems>