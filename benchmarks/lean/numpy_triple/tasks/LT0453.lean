-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermvander2d {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) : 
    Id (Vector (Vector Float ((xdeg + 1) * (ydeg + 1))) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermvander2d_spec {n : Nat} (x y : Vector Float n) (xdeg ydeg : Nat) :
    ⦃⌜True⌝⦄
    hermvander2d x y xdeg ydeg
    ⦃⇓V => ⌜-- Each row has the correct size
           (∀ k : Fin n, (V.get k).size = (xdeg + 1) * (ydeg + 1)) ∧
           -- The first column (i=0, j=0) is all ones
           (∀ k : Fin n, (V.get k).get ⟨0, Nat.zero_lt_of_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero xdeg) (Nat.succ_ne_zero ydeg))⟩ = 1) ∧
           -- Column indexing follows row-major order: (ydeg + 1)*i + j
           (∀ k : Fin n, ∀ i : Fin (xdeg + 1), ∀ j : Fin (ydeg + 1),
             -- We need a proof that the column index is valid
             ∀ (h_idx : (ydeg + 1) * i.val + j.val < (xdeg + 1) * (ydeg + 1)),
             let col_idx : Fin ((xdeg + 1) * (ydeg + 1)) := ⟨(ydeg + 1) * i.val + j.val, h_idx⟩
             ∃ (H_i_x H_j_y : Float),
               -- H_i_x is the i-th Hermite polynomial evaluated at x[k]
               (i.val = 0 → H_i_x = 1) ∧
               (i.val = 1 → H_i_x = 2 * x.get k) ∧
               (i.val ≥ 2 → ∃ (H_prev H_prev2 : Float),
                 H_i_x = 2 * x.get k * H_prev - 2 * Float.ofNat (i.val - 1) * H_prev2) ∧
               -- H_j_y is the j-th Hermite polynomial evaluated at y[k]
               (j.val = 0 → H_j_y = 1) ∧
               (j.val = 1 → H_j_y = 2 * y.get k) ∧
               (j.val ≥ 2 → ∃ (H_prev H_prev2 : Float),
                 H_j_y = 2 * y.get k * H_prev - 2 * Float.ofNat (j.val - 1) * H_prev2) ∧
               -- The matrix element is the product
               (V.get k).get col_idx = H_i_x * H_j_y) ∧
           -- Additional property: The matrix columns correspond to coefficient ordering
           -- c_00, c_01, c_02, ..., c_10, c_11, ...
           (∀ k : Fin n, ∀ idx : Fin ((xdeg + 1) * (ydeg + 1)),
             let i := idx.val / (ydeg + 1)
             let j := idx.val % (ydeg + 1)
             ∀ (h_i : i < xdeg + 1) (h_j : j < ydeg + 1),
             idx.val = (ydeg + 1) * i + j)⌝⦄ := by
  sorry
-- </vc-theorems>