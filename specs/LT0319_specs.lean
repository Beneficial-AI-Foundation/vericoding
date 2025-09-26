-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def frexp {n : Nat} (x : Vector Float n) : Id (Vector Float n × Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem frexp_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    frexp x
    ⦃⇓result => ⌜let (mantissa, exponent) := result
                 -- Element-wise properties (length is preserved by type)
                 ∀ i : Fin n,
                   -- Zero case
                   (x.get i = 0 → mantissa.get i = 0 ∧ exponent.get i = 0) ∧
                   -- Non-zero finite case
                   (x.get i ≠ 0 ∧ Float.isFinite (x.get i) → 
                     -- Reconstruction property
                     x.get i = mantissa.get i * Float.pow 2.0 (Float.ofInt (exponent.get i)) ∧
                     -- Normalization property
                     0.5 ≤ Float.abs (mantissa.get i) ∧ 
                     Float.abs (mantissa.get i) < 1.0 ∧
                     -- Sign preservation
                     (x.get i > 0 → mantissa.get i > 0) ∧
                     (x.get i < 0 → mantissa.get i < 0)) ∧
                   -- Special values case
                   ((Float.isInf (x.get i) ∨ Float.isNaN (x.get i)) → 
                     mantissa.get i = x.get i ∧ exponent.get i = 0)⌝⦄ := by
  sorry
-- </vc-theorems>