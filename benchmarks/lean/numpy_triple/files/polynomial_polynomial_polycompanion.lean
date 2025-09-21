-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polycompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polycompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_leading : c.get ⟨n + 1, sorry⟩ ≠ 0) :
    ⦃⌜c.get ⟨n + 1, sorry⟩ ≠ 0⌝⦄
    polycompanion c
    ⦃⇓result => ⌜∀ i j : Fin (n + 1),
        (result.get i).get j = 
          if i.val + 1 = j.val ∧ i.val < n then 
            1
          else if i.val = n then 
            -(c.get ⟨j.val, sorry⟩) / (c.get ⟨n + 1, sorry⟩)
          else 
            0⌝⦄ := by
  sorry
-- </vc-theorems>