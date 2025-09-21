-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arange {n : Nat} (start stop step : Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arange_spec {n : Nat} (start stop step : Float) 
    (h_step_nonzero : step ≠ 0) :
    ⦃⌜step ≠ 0⌝⦄
    arange start stop step
    ⦃⇓result => ⌜(n = 0 → (step > 0 ∧ start ≥ stop) ∨ (step < 0 ∧ start ≤ stop)) ∧
                (n > 0 → (∀ i : Fin n, result.get i = start + (i.val.toFloat) * step) ∧
                         (step > 0 → start < stop ∧ ∀ i : Fin n, result.get i < stop) ∧
                         (step < 0 → start > stop ∧ ∀ i : Fin n, result.get i > stop))⌝⦄ := by
  sorry
-- </vc-theorems>