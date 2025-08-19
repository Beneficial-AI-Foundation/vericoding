import Std.Do.Triple
import Std.Tactic.Do

  "name": "numpy.expand_dims",
  "category": "Changing Dimensions",
  "description": "Expand the shape of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.expand_dims.html",
  "doc": "Expand the shape of an array.\n\nInsert a new axis that will appear at the `axis` position in the expanded\narray shape.\n\nParameters\n----------\na : array_like\n    Input array.\naxis : int or tuple of ints\n    Position in the expanded axes where the new axis (or axes) is placed.\n\nReturns\n-------\nresult : ndarray\n    View of `a` with the number of dimensions increased.\n\nExamples\n--------\n>>> x = np.array([1, 2])\n>>> x.shape\n(2,)\n>>> y = np.expand_dims(x, axis=0)\n>>> y\narray([[1, 2]])\n>>> y.shape\n(1, 2)\n>>> y = np.expand_dims(x, axis=1)\n>>> y\narray([[1],\n       [2]])\n>>> y.shape\n(2, 1)",
  "code": "# Implementation in numpy/lib/_shape_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.expand_dims(a, axis)"
-/

open Std.Do

/-- Represents the result of expanding dimensions of a vector.
    For axis=0, we get a 1×n matrix (row vector).
    For axis=1, we get an n×1 matrix (column vector). -/
inductive ExpandedVector (T : Type) (n : Nat) where
  | rowVector : Vector T n → ExpandedVector T n      -- axis=0: shape (1, n)
  | columnVector : Vector T n → ExpandedVector T n   -- axis=1: shape (n, 1)

/-- Expand the shape of a vector by inserting a new axis at the specified position.
    axis=0 creates a row vector (1×n), axis=1 creates a column vector (n×1). -/
def expand_dims {n : Nat} (a : Vector T n) (axis : Nat) : Id (ExpandedVector T n) :=
  if axis = 0 then
    pure (ExpandedVector.rowVector a)
  else
    pure (ExpandedVector.columnVector a)

-- LLM HELPER
lemma axis_eq_one_of_le_one_and_ne_zero {axis : Nat} (h_axis : axis ≤ 1) (h_ne : axis ≠ 0) : axis = 1 := by
  cases' Nat.lt_or_eq_of_le h_axis with h1 h2
  · cases' Nat.lt_or_eq_of_le h1 with h3 h4
    · simp at h3
    · exact h4
  · exact h2

/-- Specification: expand_dims preserves all elements and adds a new dimension at the specified axis.
    The function creates a view with increased dimensions while maintaining element order and values. -/
theorem expand_dims_spec {n : Nat} (a : Vector T n) (axis : Nat) (h_axis : axis ≤ 1) :
    ⦃⌜axis ≤ 1⌝⦄
    expand_dims a axis
    ⦃⇓result => ⌜match result with
                | ExpandedVector.rowVector v => axis = 0 ∧ v = a
                | ExpandedVector.columnVector v => axis = 1 ∧ v = a⌝⦄ := by
  simp [expand_dims]
  split_ifs with h
  · simp [h]
  · simp
    exact axis_eq_one_of_le_one_and_ne_zero h_axis h