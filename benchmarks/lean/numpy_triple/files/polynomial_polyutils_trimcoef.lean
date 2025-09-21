-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def trimcoef {n : Nat} (c : Vector Float n) (tol : Float) : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trimcoef_spec {n : Nat} (c : Vector Float n) (tol : Float) 
    (h_tol_nonneg : tol ≥ 0) :
    ⦃⌜tol ≥ 0⌝⦄
    trimcoef c tol
    ⦃⇓result => ⌜
      -- Basic sanity: result is non-empty
      (∃ m : Nat, m ≥ 1) ∧
      -- Special case: if all input coefficients are small, return single zero
      ((∀ i : Fin n, Float.abs (c.get i) ≤ tol) → 
        (∃ h : 0 < n + 1, result.get ⟨0, h⟩ = 0)) ∧
      -- General case: preserve coefficients up to the last significant one
      ((∃ i : Fin n, Float.abs (c.get i) > tol) → 
        (∃ last_significant : Fin n, 
          -- last_significant is the rightmost index with coefficient > tol
          (Float.abs (c.get last_significant) > tol) ∧
          (∀ j : Fin n, j > last_significant → Float.abs (c.get j) ≤ tol) ∧
          -- All coefficients up to last_significant are preserved in order
          (∀ i : Fin n, i.val ≤ last_significant.val → 
            (∃ h : i.val < n + 1, result.get ⟨i.val, h⟩ = c.get i)))) ∧
      -- Mathematical correctness: no large coefficients are lost
      (∀ i : Fin n, Float.abs (c.get i) > tol → 
        (∃ j : Fin (n + 1), result.get j = c.get i)) ∧
      -- Trimming guarantee: result has no trailing large coefficients
      (∀ i : Fin (n + 1), (∀ j : Fin (n + 1), j > i → Float.abs (result.get j) ≤ tol) →
        (∀ k : Fin (n + 1), k ≥ i → Float.abs (result.get k) ≤ tol))
    ⌝⦄ := by
  sorry
-- </vc-theorems>