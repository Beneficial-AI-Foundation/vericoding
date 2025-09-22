-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unravel_index {n d : Nat} (indices : Vector Nat n) (shape : Vector Nat d) : Id (Vector (Vector Nat d) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unravel_index_spec {n d : Nat} (indices : Vector Nat n) (shape : Vector Nat d) 
    (h_shape_pos : ∀ i : Fin d, shape.get i > 0)
    (h_indices_valid : ∀ i : Fin n, indices.get i < (shape.toList.foldl (· * ·) 1)) :
    ⦃⌜(∀ i : Fin d, shape.get i > 0) ∧ (∀ i : Fin n, indices.get i < (shape.toList.foldl (· * ·) 1))⌝⦄
    unravel_index indices shape
    ⦃⇓coords => ⌜
      -- Each result has the same size as the number of dimensions
      (∀ i : Fin n, (coords.get i).size = d) ∧
      -- Each coordinate is within bounds for its dimension
      (∀ i : Fin n, ∀ j : Fin d, (coords.get i).get j < shape.get j) ∧
      -- Uniqueness: different flat indices produce different coordinates
      (∀ i j : Fin n, i ≠ j → indices.get i ≠ indices.get j → coords.get i ≠ coords.get j)⌝⦄ := by
  sorry
-- </vc-theorems>