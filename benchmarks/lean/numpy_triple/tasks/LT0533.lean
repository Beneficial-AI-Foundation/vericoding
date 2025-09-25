-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def as_series {m n : Nat} (arr : Vector (Vector Float n) m) (trim : Bool) : 
    Id (Vector (Vector Float n) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem as_series_spec {m n : Nat} (arr : Vector (Vector Float n) m) (trim : Bool) :
    ⦃⌜True⌝⦄
    as_series arr trim
    ⦃⇓result => ⌜∀ i : Fin m, 
                  (¬trim → ∀ j : Fin n, (result.get i).get j = (arr.get i).get j) ∧
                  (trim → (∀ j : Fin n, (result.get i).get j = (arr.get i).get j ∨ 
                           (result.get i).get j = 0) ∧
                          (∃ k : Fin n, ∀ l : Fin n, l > k → (arr.get i).get l = 0))⌝⦄ := by
  sorry
-- </vc-theorems>