-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  sorry
-- </vc-theorems>