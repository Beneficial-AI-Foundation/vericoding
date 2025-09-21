-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legder {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) : Id (Vector Float (max 1 (n - m))) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legder_spec {n : Nat} (c : Vector Float n) (m : Nat) (scl : Float) (h : n ≥ 1) :
    ⦃⌜n ≥ 1⌝⦄
    legder c m scl
    ⦃⇓result => ⌜
      -- Result size is correct
      (result.size = max 1 (n - m)) ∧
      -- If m = 0, result equals input (identity operation)
      (m = 0 → result.size = n ∧ ∀ i : Fin n, ∃ j : Fin result.size, result.get j = c.get i) ∧
      -- If m >= n, result is zero vector of length 1
      (m ≥ n → result.size = 1)
    ⌝⦄ := by
  sorry
-- </vc-theorems>