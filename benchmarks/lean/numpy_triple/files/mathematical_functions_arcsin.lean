-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_arcsin {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_arcsin_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, -1 ≤ x.get i ∧ x.get i ≤ 1⌝⦄
    numpy_arcsin x
    ⦃⇓result => ⌜∀ i : Fin n, 
        result.get i = Float.asin (x.get i) ∧
        -1.5707963267948966 ≤ result.get i ∧ result.get i ≤ 1.5707963267948966 ∧
        Float.sin (result.get i) = x.get i ∧
        (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j) ∧
        (x.get i = 0 → result.get i = 0) ∧
        (x.get i = 1 → result.get i = 1.5707963267948966) ∧
        (x.get i = -1 → result.get i = -1.5707963267948966)⌝⦄ := by
  sorry
-- </vc-theorems>