-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getdomain {n : Nat} (x : Vector Float (n + 1)) : Id (Vector Float 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem getdomain_spec {n : Nat} (x : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    getdomain x
    ⦃⇓result => ⌜
      -- The minimum is less than or equal to the maximum
      result[0] ≤ result[1] ∧
      -- Every element in x is within the domain
      (∀ i : Fin (n + 1), result[0] ≤ x[i] ∧ x[i] ≤ result[1]) ∧
      -- The domain bounds are achieved by some elements in x
      (∃ i : Fin (n + 1), x[i] = result[0]) ∧
      (∃ j : Fin (n + 1), x[j] = result[1])
    ⌝⦄ := by
  sorry
-- </vc-theorems>