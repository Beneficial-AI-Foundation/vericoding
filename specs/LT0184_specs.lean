-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nditer {n : Nat} (arr : Vector Float n) : Id (Nat × Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nditer_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    nditer arr
    ⦃⇓iter => ⌜(iter.1 = 0) ∧
               (iter.2 = arr) ∧
               (iter.1 ≤ n) ∧
               (∀ i : Fin n, iter.2.get i = arr.get i)⌝⦄ := by
  sorry
-- </vc-theorems>