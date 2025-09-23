-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    minimum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = min (x1.get i) (x2.get i) ∧
                 -- Commutativity property
                 (minimum x1 x2).get i = (minimum x2 x1).get i ∧
                 -- Bounded property: result is bounded by inputs
                 result.get i ≤ x1.get i ∧ result.get i ≤ x2.get i ∧
                 -- Definitional property: result equals one of the inputs
                 (result.get i = x1.get i ∨ result.get i = x2.get i)⌝⦄ := by
  sorry
-- </vc-theorems>