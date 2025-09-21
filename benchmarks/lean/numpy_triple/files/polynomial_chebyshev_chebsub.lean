-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebsub {n : Nat} (c1 c2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebsub_spec {n : Nat} (c1 c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    chebsub c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = c1.get i - c2.get i) ∧
                 (∀ i : Fin n, (chebsub c2 c1).get i = -(result.get i)) ∧
                 (∀ i : Fin n, (chebsub c1 c1).get i = 0)⌝⦄ := by
  sorry
-- </vc-theorems>