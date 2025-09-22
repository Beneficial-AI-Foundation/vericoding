-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermegrid2d {nx ny : Nat} {deg_x deg_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float deg_y) deg_x) : 
    Id (Vector (Vector Float ny) nx) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermegrid2d_spec {nx ny : Nat} {deg_x deg_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float deg_y) deg_x) :
    ⦃⌜True⌝⦄
    hermegrid2d x y c
    ⦃⇓result => ⌜
      -- Result has correct shape: nx rows, ny columns
      result.size = nx ∧ 
      (∀ i : Fin nx, (result.get i).size = ny) ∧
      -- Each result[i,j] represents the polynomial evaluation at point (x[i], y[j])
      (∀ i : Fin nx, ∀ j : Fin ny, 
        -- If coefficient matrix is empty in either dimension, result is zero
        (deg_x = 0 ∨ deg_y = 0 → (result.get i).get j = 0) ∧
        -- Otherwise, result represents the 2D HermiteE polynomial evaluation
        -- at the Cartesian product point (x[i], y[j])
        (deg_x > 0 ∧ deg_y > 0 → 
          -- The result is the sum of all coefficient terms multiplied by 
          -- the corresponding HermiteE polynomial values
          ∃ (hermite_e : Float → Nat → Float), 
            (result.get i).get j = 
            (List.range deg_x).foldl (fun acc k_x => 
              acc + (List.range deg_y).foldl (fun acc_y k_y => 
                acc_y + (c.get ⟨k_x, sorry⟩).get ⟨k_y, sorry⟩ * 
                        hermite_e (x.get i) k_x * hermite_e (y.get j) k_y
              ) 0
            ) 0))
    ⌝⦄ := by
  sorry
-- </vc-theorems>