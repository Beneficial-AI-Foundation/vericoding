-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all {n : Nat} (a : Vector Float n) : Id Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    all a
    ⦃⇓result => ⌜(result = true ↔ ∀ i : Fin n, a.get i ≠ 0) ∧
                  (n = 0 → result = true) ∧
                  ((∃ i : Fin n, a.get i = 0) → result = false) ∧
                  (∀ i : Fin n, a.get i ≠ 0 → result = true)⌝⦄ := by
  sorry
-- </vc-theorems>