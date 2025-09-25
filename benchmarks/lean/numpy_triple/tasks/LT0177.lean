-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def indices (n : Nat) : Id (Vector (Vector Nat n) 1) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem indices_spec (n : Nat) :
    ⦃⌜True⌝⦄
    indices n
    ⦃⇓grid => ⌜grid.size = 1 ∧ 
              (∀ i : Fin n, (grid.get ⟨0, by simp⟩).get i = i.val) ∧
              (∀ i j : Fin n, i < j → (grid.get ⟨0, by simp⟩).get i < (grid.get ⟨0, by simp⟩).get j)⌝⦄ := by
  sorry
-- </vc-theorems>