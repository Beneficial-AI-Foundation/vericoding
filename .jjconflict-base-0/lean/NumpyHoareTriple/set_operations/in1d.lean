import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.in1d",
  "category": "Testing membership",
  "description": "Test whether each element of a 1-D array is also present in a second array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.in1d.html",
  "doc": "Test whether each element of a 1-D array is also present in a second array.\n\n.. deprecated:: 2.0\n    Use :func:`isin` instead of `in1d` for new code.\n\nReturns a boolean array the same length as `ar1` that is True\nwhere an element of `ar1` is in `ar2` and False otherwise.\n\nParameters\n----------\nar1 : (M,) array_like\n    Input array.\nar2 : array_like\n    The values against which to test each value of `ar1`.\n\nReturns\n-------\nin1d : (M,) ndarray, bool\n    The values `ar1[in1d]` are in `ar2`.",
  "code": "def in1d(ar1, ar2, assume_unique=False, invert=False, *, kind=None):\n    # Deprecated in NumPy 2.0, 2023-08-18\n    warnings.warn(\n        \"`in1d` is deprecated. Use `np.isin` instead.\",\n        DeprecationWarning,\n        stacklevel=2\n    )\n    return _in1d(ar1, ar2, assume_unique, invert, kind=kind)"
}
-/

open Std.Do

/-- Test whether each element of a 1-D array is also present in a second array.
    Returns a boolean array the same length as `ar1` that is True where an element 
    of `ar1` is in `ar2` and False otherwise. -/
def in1d {α : Type} {m n : Nat} [DecidableEq α] (ar1 : Vector α m) (ar2 : Vector α n) : Id (Vector Bool m) :=
  sorry

/-- Specification: in1d tests membership of each element of ar1 in ar2.
    The result is a boolean vector of the same length as ar1, where each element
    indicates whether the corresponding element of ar1 is present in ar2. -/
theorem in1d_spec {α : Type} {m n : Nat} [DecidableEq α] (ar1 : Vector α m) (ar2 : Vector α n) :
    ⦃⌜True⌝⦄
    in1d ar1 ar2
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = true ↔ ∃ j : Fin n, ar1.get i = ar2.get j⌝⦄ := by
  sorry