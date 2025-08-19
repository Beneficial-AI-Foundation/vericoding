import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.newaxis",
  "category": "Indexing helpers",
  "description": "A convenient alias for None, useful for indexing arrays",
  "url": "https://numpy.org/doc/stable/reference/constants.html#numpy.newaxis",
  "doc": "newaxis is an alias for None and is used to expand the dimensions of an array.\n\nExamples:\n>>> a = np.array([1, 2, 3])\n>>> a.shape\n(3,)\n>>> a[:, np.newaxis].shape\n(3, 1)\n>>> a[np.newaxis, :].shape\n(1, 3)",
  "code": "# Defined in numeric.py\nnewaxis = None"
}
-/

open Std.Do

/-- Represents the newaxis constant used for dimension expansion.
    In NumPy, newaxis is used in indexing to add new dimensions to arrays.
    For our Vector-based implementation, we model this as a function that
    converts a 1D vector into a 2D vector (matrix) with either shape (n, 1) or (1, n). -/
inductive NewAxis where
  | newaxis

/-- Expands a vector to a column matrix (n × 1) using newaxis.
    This models the behavior of a[:, np.newaxis] which converts
    a 1D array of shape (n,) to a 2D array of shape (n, 1). -/
def expandToColumn {T : Type} {n : Nat} (v : Vector T n) (axis : NewAxis) : Id (Vector (Vector T 1) n) :=
  Id.mk (Vector.mk (Array.mk (List.range n).map (fun i => 
    Vector.mk (Array.mk [v.get ⟨i, by simp [List.mem_range]⟩]))))

/-- Specification: expandToColumn creates a column matrix where each element
    is a singleton vector containing the corresponding element from the input vector.
    
    Mathematical property:
    - The resulting matrix has shape (n, 1)
    - Each row contains exactly one element from the original vector
    - result[i][0] = v[i] for all valid indices -/
theorem expandToColumn_spec {T : Type} {n : Nat} (v : Vector T n) (axis : NewAxis) :
    ⦃⌜True⌝⦄
    expandToColumn v axis
    ⦃⇓result => ⌜∀ i : Fin n, 
                   (result.get i).size = 1 ∧ 
                   (result.get i).get ⟨0, by simp⟩ = v.get i⌝⦄ := by
  apply Std.Do.Triple.pure_spec
  intro i
  simp [expandToColumn]
  constructor
  · simp [Vector.get, Vector.mk, Array.mk, List.get_range]
  · simp [Vector.get, Vector.mk, Array.mk, List.get_range, List.get_map]