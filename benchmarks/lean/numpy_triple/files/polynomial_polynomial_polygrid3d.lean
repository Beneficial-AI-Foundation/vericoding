-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polygrid3d {nx ny nz : Nat} {degree_x degree_y degree_z : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float (degree_z + 1)) (degree_y + 1)) (degree_x + 1)) : 
    Id (Vector (Vector (Vector Float nz) ny) nx) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polygrid3d_spec {nx ny nz : Nat} {degree_x degree_y degree_z : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) (z : Vector Float nz)
    (c : Vector (Vector (Vector Float (degree_z + 1)) (degree_y + 1)) (degree_x + 1)) :
    ⦃⌜True⌝⦄
    polygrid3d x y z c
    ⦃⇓result => ⌜∀ i : Fin nx, ∀ j : Fin ny, ∀ k : Fin nz,
      ∃ (val : Float), ((result.get i).get j).get k = val ∧
      ∀ dx : Fin (degree_x + 1), ∀ dy : Fin (degree_y + 1), ∀ dz : Fin (degree_z + 1),
      ∃ (term : Float), term = ((c.get dx).get dy).get dz * (x.get i) ^ (dx.val.toFloat) * (y.get j) ^ (dy.val.toFloat) * (z.get k) ^ (dz.val.toFloat)⌝⦄ := by
  sorry
-- </vc-theorems>