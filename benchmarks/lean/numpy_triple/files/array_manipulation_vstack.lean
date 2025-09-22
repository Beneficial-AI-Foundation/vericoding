-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vstack {n : Nat} (a b : Vector Float n) : Id (Vector (Vector Float n) 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vstack_spec {n : Nat} (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    vstack a b
    ⦃⇓result => ⌜(∀ j : Fin n, (result.get 0).get j = a.get j) ∧
                 (∀ j : Fin n, (result.get 1).get j = b.get j)⌝⦄ := by
  sorry
-- </vc-theorems>