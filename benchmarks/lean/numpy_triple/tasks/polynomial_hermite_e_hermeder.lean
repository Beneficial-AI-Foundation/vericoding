-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermeder {n : Nat} (c : Vector Float (n + 1)) (m : Nat) (scl : Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermeder_spec {n : Nat} (c : Vector Float (n + 1)) (m : Nat) (scl : Float) 
    (h_pos_scl : scl > 0) (h_pos_m : m > 0) :
    ⦃⌜scl > 0 ∧ m > 0⌝⦄
    hermeder c m scl
    ⦃⇓result => ⌜
      -- For single differentiation (m=1), each coefficient follows the derivative rule
      (m = 1 → ∀ i : Fin n, result.get i = (i.val.toFloat + 1.0) * scl * c.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
      -- For multiple differentiation, the scaling factor is applied m times
      (∀ i : Fin n, Float.abs (result.get i) ≤ Float.abs scl * (n.toFloat + 1.0) * 10.0) ∧
      -- If all input coefficients are zero, result is zero
      (∀ i : Fin (n + 1), c.get i = 0 → ∀ j : Fin n, result.get j = 0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>