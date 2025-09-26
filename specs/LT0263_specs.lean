-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isclose {n : Nat} (a b : Vector Float n) (rtol : Float) (atol : Float) (equal_nan : Bool) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isclose_spec {n : Nat} (a b : Vector Float n) (rtol : Float) (atol : Float) (equal_nan : Bool) 
    (h_rtol_nonneg : rtol ≥ 0) (h_atol_nonneg : atol ≥ 0) :
    ⦃⌜rtol ≥ 0 ∧ atol ≥ 0⌝⦄
    isclose a b rtol atol equal_nan
    ⦃⇓result => ⌜∀ i : Fin n, 
        -- Core tolerance check for finite values
        (Float.isFinite (a.get i) ∧ Float.isFinite (b.get i) → 
         (result.get i = true ↔ 
          Float.abs (a.get i - b.get i) ≤ atol + rtol * Float.abs (b.get i))) ∧
        -- Infinite values are equal if they match exactly
        (¬Float.isFinite (a.get i) ∨ ¬Float.isFinite (b.get i) → 
         (result.get i = true ↔ a.get i = b.get i)) ∧
        -- NaN handling depends on equal_nan parameter
        ((a.get i).isNaN ∧ (b.get i).isNaN → 
         (result.get i = true ↔ equal_nan = true)) ∧
        -- Asymmetric property: uses b as reference value
        (result.get i = false ↔ 
         (Float.isFinite (a.get i) ∧ Float.isFinite (b.get i) ∧ 
          Float.abs (a.get i - b.get i) > atol + rtol * Float.abs (b.get i)) ∨
         (¬Float.isFinite (a.get i) ∨ ¬Float.isFinite (b.get i)) ∧ a.get i ≠ b.get i ∨
         ((a.get i).isNaN ∧ (b.get i).isNaN ∧ equal_nan = false))⌝⦄ := by
  sorry
-- </vc-theorems>