-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legint {n : Nat} (c : Vector Float n) (k : Float) (lbnd : Float) (scl : Float) 
    : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legint_spec {n : Nat} (c : Vector Float n) (k : Float) (lbnd : Float) (scl : Float) 
    (h_scl_nonzero : scl ≠ 0) :
    ⦃⌜scl ≠ 0⌝⦄
    legint c k lbnd scl
    ⦃⇓result => ⌜
      -- The result has the correct size (degree increased by 1)
      result.size = n + 1 ∧
      -- Integration preserves essential mathematical properties
      (∀ i : Fin (n + 1), 
        -- All coefficients are finite and well-defined after integration
        ∃ val : Float, result.get i = val) ∧
      -- The scaling factor affects all coefficients consistently
      (scl ≠ 1 → ∃ scaled_vals : Vector Float (n + 1), 
        ∀ i : Fin (n + 1), result.get i = scl * scaled_vals.get i) ∧
      -- Integration constant affects the constant term
      (k ≠ 0 → result.get ⟨0, Nat.zero_lt_succ n⟩ = 
        result.get ⟨0, Nat.zero_lt_succ n⟩ + k)
    ⌝⦄ := by
  sorry
-- </vc-theorems>