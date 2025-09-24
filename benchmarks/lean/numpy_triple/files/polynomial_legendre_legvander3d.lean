-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legvander3d {n : Nat} (x y z : Vector Float n) (deg_x deg_y deg_z : Nat) : 
    Id (Vector (Vector Float ((deg_x + 1) * (deg_y + 1) * (deg_z + 1))) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legvander3d_spec {n : Nat} (x y z : Vector Float n) (deg_x deg_y deg_z : Nat) :
    ⦃⌜True⌝⦄
    legvander3d x y z deg_x deg_y deg_z
    ⦃⇓result => ⌜
      -- Matrix has correct dimensions
      (∀ i : Fin n, ∀ j : Fin ((deg_x + 1) * (deg_y + 1) * (deg_z + 1)), 
        ∃ val : Float, (result.get i).get j = val) ∧
      -- First column corresponds to L_0(x) * L_0(y) * L_0(z) = 1 * 1 * 1 = 1
      (∀ i : Fin n, (result.get i).get ⟨0, sorry⟩ = 1) ∧
      -- Entries are products of Legendre polynomial evaluations
      (∀ i : Fin n, ∀ p : Fin (deg_x + 1), ∀ q : Fin (deg_y + 1), ∀ r : Fin (deg_z + 1), 
        let col_idx := (deg_y + 1) * (deg_z + 1) * p.val + (deg_z + 1) * q.val + r.val
        col_idx < (deg_x + 1) * (deg_y + 1) * (deg_z + 1) →
        ∃ L_p_x L_q_y L_r_z : Float, 
          (result.get i).get ⟨col_idx, sorry⟩ = L_p_x * L_q_y * L_r_z)
    ⌝⦄ := by
  sorry
-- </vc-theorems>