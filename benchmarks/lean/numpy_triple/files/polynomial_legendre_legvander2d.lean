-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legvander2d {n : Nat} (x y : Vector Float n) (deg_x deg_y : Nat) : Id (Vector (Vector Float ((deg_x + 1) * (deg_y + 1))) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legvander2d_spec {n : Nat} (x y : Vector Float n) (deg_x deg_y : Nat) :
    ⦃⌜True⌝⦄
    legvander2d x y deg_x deg_y
    ⦃⇓result => ⌜
      -- Matrix has correct dimensions
      (∀ i : Fin n, ∀ j : Fin ((deg_x + 1) * (deg_y + 1)), ∃ val : Float, (result.get i).get j = val) ∧
      -- First column corresponds to L_0(x) * L_0(y) = 1 * 1 = 1
      (∀ i : Fin n, (result.get i).get ⟨0, sorry⟩ = 1) ∧
      -- Entries are products of Legendre polynomial evaluations
      (∀ i : Fin n, ∀ p : Fin (deg_x + 1), ∀ q : Fin (deg_y + 1), 
        let col_idx := (deg_y + 1) * p.val + q.val
        col_idx < (deg_x + 1) * (deg_y + 1) →
        ∃ L_p_x L_q_y : Float, 
          (result.get i).get ⟨col_idx, sorry⟩ = L_p_x * L_q_y)
    ⌝⦄ := by
  sorry
-- </vc-theorems>