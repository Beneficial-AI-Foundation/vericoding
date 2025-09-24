-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nonzero {n : Nat} (a : Vector Int n) : Id Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nonzero_spec {n : Nat} (a : Vector Int n) :
    ⦃⌜True⌝⦄
    count_nonzero a
    ⦃⇓count => ⌜count ≤ n ∧ 
                (n = 0 → count = 0) ∧
                (∀ i : Fin n, a.get i = 0) → count = 0 ∧
                (∀ i : Fin n, a.get i ≠ 0) → count = n ∧
                (∃ i : Fin n, a.get i ≠ 0) → count > 0 ∧
                (∃ i : Fin n, a.get i = 0) → count < n⌝⦄ := by
  sorry
-- </vc-theorems>