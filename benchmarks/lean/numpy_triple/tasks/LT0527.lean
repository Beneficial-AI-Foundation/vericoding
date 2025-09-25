-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyval2d {m nx ny : Nat} (x y : Vector Float m) 
    (c : Vector (Vector Float (ny + 1)) (nx + 1)) : Id (Vector Float m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyval2d_spec {m nx ny : Nat} (x y : Vector Float m) 
    (c : Vector (Vector Float (ny + 1)) (nx + 1)) :
    ⦃⌜True⌝⦄
    polyval2d x y c
    ⦃⇓result => ⌜∀ k : Fin m, ∃ (poly_val : Float), result.get k = poly_val ∧
                  -- Constant term property: when both degrees are 0
                  (nx = 0 ∧ ny = 0 → poly_val = (c.get ⟨0, Nat.zero_lt_succ _⟩).get ⟨0, Nat.zero_lt_succ _⟩) ∧
                  -- Zero coefficient property: if all coefficients are zero, result is zero
                  (∀ i : Fin (nx + 1), ∀ j : Fin (ny + 1), (c.get i).get j = 0 → poly_val = 0) ∧
                  -- Evaluation at origin gives constant term
                  (x.get k = 0 ∧ y.get k = 0 → poly_val = (c.get ⟨0, Nat.zero_lt_succ _⟩).get ⟨0, Nat.zero_lt_succ _⟩)⌝⦄ := by
  sorry
-- </vc-theorems>