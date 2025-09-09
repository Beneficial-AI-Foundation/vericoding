/- 
{
  "name": "numpy.interp",
  "description": "One-dimensional linear interpolation for monotonically increasing sample points",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.interp.html",
  "doc": "One-dimensional linear interpolation for monotonically increasing sample points.\n\nReturns the one-dimensional piecewise linear interpolant to a function with given discrete data points (xp, fp), evaluated at x.",
}
-/

/-  One-dimensional linear interpolation for monotonically increasing sample points.
    Returns the one-dimensional piecewise linear interpolant to a function with given
    discrete data points (xp, fp), evaluated at x. -/

/-  Specification: interp performs linear interpolation between discrete data points -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def interp {n m : Nat} (x : Vector Float n) (xp : Vector Float (m + 1)) (fp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) : Id (Vector Float n) :=
  sorry

theorem interp_spec {n m : Nat} (x : Vector Float n) (xp : Vector Float (m + 1)) (fp : Vector Float (m + 1)) 
    (h_increasing : ∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j) :
    ⦃⌜∀ i j : Fin (m + 1), i < j → xp.get i < xp.get j⌝⦄
    interp x xp fp h_increasing
    ⦃⇓result => ⌜
      -- Each interpolated value is computed correctly
      ∀ k : Fin n, 
        -- For points outside the left range, use left boundary value
        (x.get k ≤ xp.get ⟨0, sorry⟩ → result.get k = fp.get ⟨0, sorry⟩) ∧
        -- For points outside the right range, use right boundary value
        (x.get k ≥ xp.get ⟨m, sorry⟩ → result.get k = fp.get ⟨m, sorry⟩) ∧
        -- For points exactly at data points, return exact values
        (∀ i : Fin (m + 1), x.get k = xp.get i → result.get k = fp.get i) ∧
        -- For points within the range, value is between adjacent data points
        (∀ i : Fin m, 
          xp.get ⟨i.val, sorry⟩ ≤ x.get k ∧ x.get k ≤ xp.get ⟨i.val + 1, sorry⟩ →
          ∃ t : Float, 0 ≤ t ∧ t ≤ 1 ∧ 
          result.get k = fp.get ⟨i.val, sorry⟩ + t * (fp.get ⟨i.val + 1, sorry⟩ - fp.get ⟨i.val, sorry⟩))
    ⌝⦄ := by
  sorry
