-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trapezoid {n : Nat} (y : Vector Float (n + 1)) (dx : Float) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trapezoid_spec {n : Nat} (y : Vector Float (n + 1)) (dx : Float) 
    (h_pos : dx > 0) :
    ⦃⌜dx > 0⌝⦄
    trapezoid y dx
    ⦃⇓result => ⌜-- Sanity check: result should be finite
                 ¬result.isNaN ∧ ¬result.isInf ∧
                 -- Mathematical property: For a constant function, trapezoid rule is exact
                 (∀ i : Fin (n + 1), y.get i = y.get ⟨0, by simp⟩ → 
                  result = dx * (n.toFloat) * y.get ⟨0, by simp⟩) ∧
                 -- Linearity property: trapezoid is linear in y
                 (∀ (y1 y2 : Vector Float (n + 1)) (c1 c2 : Float),
                  (∀ i : Fin (n + 1), y.get i = c1 * y1.get i + c2 * y2.get i) →
                  result = c1 * (trapezoid y1 dx).run + c2 * (trapezoid y2 dx).run) ∧
                 -- Monotonicity: if all y values are non-negative, result is non-negative
                 (∀ i : Fin (n + 1), y.get i ≥ 0 → result ≥ 0)⌝⦄ := by
  sorry
-- </vc-theorems>