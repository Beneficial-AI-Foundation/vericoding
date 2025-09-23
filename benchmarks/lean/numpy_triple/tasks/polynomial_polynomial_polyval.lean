-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyval {m n : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) : Id (Vector Float m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyval_spec {m n : Nat} (x : Vector Float m) (c : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    polyval x c
    ⦃⇓result => ⌜∀ i : Fin m, ∃ (poly_val : Float), result.get i = poly_val ∧
                  (n = 0 → poly_val = c.get ⟨0, Nat.zero_lt_succ _⟩) ∧
                  (∀ j : Fin (n + 1), c.get j = 0 → poly_val = 0)⌝⦄ := by
  sorry
-- </vc-theorems>