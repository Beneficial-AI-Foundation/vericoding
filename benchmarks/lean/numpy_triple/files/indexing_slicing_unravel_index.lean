/- 
{
  "name": "numpy.unravel_index",
  "category": "Index generation",
  "description": "Converts a flat index or array of flat indices into a tuple of coordinate arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.unravel_index.html",
  "doc": "Converts a flat index or array of flat indices into a tuple of coordinate arrays.\n\nParameters\n----------\nindices : array_like\n    An integer array whose elements are indices into the flattened version of an array of dimensions shape.\nshape : tuple of ints\n    The shape of the array to use for unraveling indices.\norder : {'C', 'F'}, optional\n    Determines whether the indices should be viewed as indexing in row-major (C-style) or column-major (Fortran-style) order.\n\nReturns\n-------\nunraveled_coords : tuple of ndarray\n    Each array in the tuple has the same shape as the indices array.",
}
-/

/-  Converts flat indices into multi-dimensional coordinates for a given shape.
    This is the inverse operation of ravel_multi_index. -/

/-  Specification: unravel_index converts flat indices to multi-dimensional coordinates
    such that the coordinates are valid for the given shape and represent the correct
    positions in the multi-dimensional array. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def unravel_index {n d : Nat} (indices : Vector Nat n) (shape : Vector Nat d) : Id (Vector (Vector Nat d) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
-- <vc-proof>
  sorry
-- </vc-proof>
