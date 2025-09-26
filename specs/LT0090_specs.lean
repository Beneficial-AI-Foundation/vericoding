-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def right_shift {n : Nat} (x1 x2 : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem right_shift_spec {n : Nat} (x1 x2 : Vector Int n) 
    (h_shift_nonneg : ∀ i : Fin n, x2.get i ≥ 0) :
    ⦃⌜∀ i : Fin n, x2.get i ≥ 0⌝⦄
    right_shift x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, 
        -- For non-negative values, right shift equals division by 2^shift
        (x1.get i ≥ 0 → result.get i = x1.get i / (2 ^ (x2.get i).natAbs)) ∧
        -- For negative values, we use arithmetic right shift (sign extension)
        -- This maintains the property that x >> k = floor(x / 2^k)
        (x1.get i < 0 → result.get i = Int.ediv (x1.get i) (2 ^ (x2.get i).natAbs)) ∧
        -- Identity property: shifting by 0 returns the original value
        (x2.get i = 0 → result.get i = x1.get i) ∧
        -- Sign preservation: the sign of the result matches the sign of the input
        ((x1.get i > 0 → result.get i ≥ 0) ∧ 
         (x1.get i < 0 → result.get i ≤ 0) ∧
         (x1.get i = 0 → result.get i = 0)) ∧
        -- Bounded result: |result| ≤ |input| for any non-negative shift
        (Int.natAbs (result.get i) ≤ Int.natAbs (x1.get i))⌝⦄ := by
  sorry
-- </vc-theorems>