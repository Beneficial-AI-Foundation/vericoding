-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spacing {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spacing_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    spacing x
    ⦃⇓result => ⌜∀ i : Fin n, 
                    (¬(x.get i).isInf ∧ ¬(x.get i).isNaN → result.get i > 0) ∧
                    (x.get i = 1.0 → result.get i > 0) ∧
                    ((x.get i).isInf ∨ (x.get i).isNaN → (result.get i).isNaN) ∧
                    (¬(x.get i).isInf ∧ ¬(x.get i).isNaN → result.get i > 0) ∧
                    (∀ j : Fin n, (x.get i).abs = (x.get j).abs → result.get i = result.get j)⌝⦄ := by
  sorry
-- </vc-theorems>