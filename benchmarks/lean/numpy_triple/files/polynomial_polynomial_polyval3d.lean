-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyval3d {n : Nat} {deg_x deg_y deg_z : Nat} 
    (x y z : Vector Float n) 
    (c : Vector (Vector (Vector Float (deg_z + 1)) (deg_y + 1)) (deg_x + 1)) : 
    Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyval3d_spec {n : Nat} {deg_x deg_y deg_z : Nat} 
    (x y z : Vector Float n) 
    (c : Vector (Vector (Vector Float (deg_z + 1)) (deg_y + 1)) (deg_x + 1)) :
    ⦃⌜True⌝⦄
    polyval3d x y z c
    ⦃⇓result => ⌜∀ p : Fin n, 
                  ∃ val : Float, result.get p = val ∧ 
                  (deg_x = 0 ∧ deg_y = 0 ∧ deg_z = 0 → 
                   val = ((c.get ⟨0, sorry⟩).get ⟨0, sorry⟩).get ⟨0, sorry⟩)⌝⦄ := by
  sorry
-- </vc-theorems>