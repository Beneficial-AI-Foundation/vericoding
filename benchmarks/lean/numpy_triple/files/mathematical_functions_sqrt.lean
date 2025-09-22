-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sqrt_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    sqrt x
    ⦃⇓result => ⌜∀ i : Fin n,
      (x.get i ≥ 0 → 
        result.get i * result.get i = x.get i ∧ 
        result.get i ≥ 0) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (x.get i = 1 → result.get i = 1)⌝⦄ := by
  sorry
-- </vc-theorems>