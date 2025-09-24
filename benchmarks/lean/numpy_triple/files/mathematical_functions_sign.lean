-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sign {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sign_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    sign x
    ⦃⇓result => ⌜∀ i : Fin n, 
      (x.get i < 0 → result.get i = -1) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (x.get i > 0 → result.get i = 1)⌝⦄ := by
  sorry
-- </vc-theorems>