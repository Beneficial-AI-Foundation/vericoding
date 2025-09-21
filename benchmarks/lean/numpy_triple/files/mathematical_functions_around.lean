-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def around {n : Nat} (a : Vector Float n) (decimals : Int := 0) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem around_spec {n : Nat} (a : Vector Float n) (decimals : Int := 0) :
    ⦃⌜True⌝⦄
    around a decimals
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Zero preservation: rounding zero gives zero
      (a.get i = 0 → result.get i = 0) ∧
      -- Order preservation: maintains ordering
      (∀ j : Fin n, a.get i ≤ a.get j → result.get i ≤ result.get j) ∧
      -- Boundedness: rounded values are close to original values
      (decimals = 0 → 
       (result.get i - 1 ≤ a.get i ∧ a.get i ≤ result.get i + 1)) ∧
      -- Symmetry: rounding negatives has expected behavior
      (a.get i ≥ 0 → result.get i ≥ 0)⌝⦄ := by
  sorry
-- </vc-theorems>