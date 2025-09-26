-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_isin {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_isin_spec {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_isin element test_elements
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = true ↔ ∃ j : Fin m, element.get i = test_elements.get j⌝⦄ := by
  sorry
-- </vc-theorems>