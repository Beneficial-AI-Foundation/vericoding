-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maximum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    maximum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = max (x1.get i) (x2.get i) ∧
                 ∀ i : Fin n, result.get i ≥ x1.get i ∧ result.get i ≥ x2.get i ∧
                 (result.get i = x1.get i ∨ result.get i = x2.get i)⌝⦄ := by
  sorry
-- </vc-theorems>