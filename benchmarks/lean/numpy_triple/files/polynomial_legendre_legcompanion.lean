-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get ⟨n + 1, by simp⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, by simp⟩ ≠ 0⌝⦄
    legcompanion c
    ⦃⇓result => ⌜
      (∀ i j : Fin (n + 1), (result.get i).get j = (result.get j).get i) ∧
      (result.size = n + 1) ∧
      (∀ i : Fin (n + 1), (result.get i).size = n + 1)
    ⌝⦄ := by
  sorry
-- </vc-theorems>