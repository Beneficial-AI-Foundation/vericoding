-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isinf {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isinf_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isinf x
    ⦃⇓result => ⌜∀ i : Fin n, 
      (result.get i = (x.get i).isInf) ∧
      (¬(x.get i).isInf → result.get i = false) ∧
      ((x.get i).isNaN → result.get i = false) ∧
      (x.get i = 0.0 → result.get i = false) ∧
      (result.get i = true → ¬(x.get i).isFinite) ∧
      (result.get i = true → ¬(x.get i).isNaN)⌝⦄ := by
  sorry
-- </vc-theorems>