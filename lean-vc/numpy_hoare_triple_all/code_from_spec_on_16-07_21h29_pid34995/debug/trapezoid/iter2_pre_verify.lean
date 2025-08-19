import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def sum_middle_terms {n : Nat} (y : Vector Float (n + 1)) : Float :=
  if n = 0 then 0 else
  (List.range n).foldl (fun acc i => acc + y.get ⟨i + 1, by simp; linarith⟩) 0

/-- Integrate using the composite trapezoidal rule with uniform spacing -/
def trapezoid {n : Nat} (y : Vector Float (n + 1)) (dx : Float) : Id Float :=
  if n = 0 then pure 0 else
  let first_term := y.get ⟨0, by simp⟩ / 2
  let last_term := y.get ⟨n, by simp⟩ / 2
  let middle_sum := sum_middle_terms y
  pure (dx * (first_term + middle_sum + last_term))

/-- Specification: trapezoid computes the definite integral using the composite trapezoidal rule
    For uniform spacing dx, the integral is approximated as:
    ∫ f(x) dx ≈ dx * (y[0]/2 + y[1] + y[2] + ... + y[n-1] + y[n]/2) -/
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
  simp [HoareTriple.bind, HoareTriple.pure]
  constructor
  · exact h_pos
  · simp [trapezoid]
    split_ifs with h
    · simp [h]
      constructor
      · simp [Float.isNaN, Float.isInf]
      · constructor
        · intros h_const
          simp [h, Nat.cast_zero, Float.zero_mul]
        · constructor
          · intros y1 y2 c1 c2 h_linear
            simp [trapezoid, h]
          · intros h_nonneg
            simp
    · simp
      constructor
      · simp [Float.isNaN, Float.isInf]
        rfl
      · constructor
        · intros h_const
          simp [sum_middle_terms]
          rfl
        · constructor
          · intros y1 y2 c1 c2 h_linear
            simp [trapezoid]
            rfl
          · intros h_nonneg
            simp [trapezoid]
            rfl