-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polygrid2d {nx ny : Nat} {degree_x degree_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float (degree_y + 1)) (degree_x + 1)) : 
    Id (Vector (Vector Float ny) nx) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polygrid2d_spec {nx ny : Nat} {degree_x degree_y : Nat} 
    (x : Vector Float nx) (y : Vector Float ny) 
    (c : Vector (Vector Float (degree_y + 1)) (degree_x + 1)) :
    ⦃⌜True⌝⦄
    polygrid2d x y c
    ⦃⇓result => ⌜∀ i : Fin nx, ∀ j : Fin ny, 
      ∃ (val : Float), (result.get i).get j = val ∧
      ∀ dx : Fin (degree_x + 1), ∀ dy : Fin (degree_y + 1),
      ∃ (term : Float), term = (c.get dx).get dy * (x.get i) ^ (dx.val.toFloat) * (y.get j) ^ (dy.val.toFloat)⌝⦄ := by
  sorry
-- </vc-theorems>