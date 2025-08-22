import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.setdiff1d",
  "category": "Set operations",
  "description": "Find the set difference of two arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.setdiff1d.html",
  "doc": "Find the set difference of two arrays.\n\nReturn the unique values in `ar1` that are not in `ar2`.\n\nParameters\n----------\nar1 : array_like\n    Input array.\nar2 : array_like\n    Input comparison array.\nassume_unique : bool\n    If True, the input arrays are both assumed to be unique, which\n    can speed up the calculation.  Default is False.\n\nReturns\n-------\nsetdiff1d : ndarray\n    1D array of values in `ar1` that are not in `ar2`. The result\n    is sorted when `assume_unique=False`, but otherwise only sorted\n    if the input is sorted.",
  "code": "def setdiff1d(ar1, ar2, assume_unique=False):\n    \"\"\"\n    Find the set difference of two arrays.\n\n    Return the unique values in `ar1` that are not in `ar2`.\n\n    Parameters\n    ----------\n    ar1 : array_like\n        Input array.\n    ar2 : array_like\n        Input comparison array.\n    assume_unique : bool\n        If True, the input arrays are both assumed to be unique, which\n        can speed up the calculation.  Default is False.\n\n    Returns\n    -------\n    setdiff1d : ndarray\n        1D array of values in `ar1` that are not in `ar2`. The result\n        is sorted when `assume_unique=False`, but otherwise only sorted\n        if the input is sorted.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> a = np.array([1, 2, 3, 2, 4, 1])\n    >>> b = np.array([3, 4, 5, 6])\n    >>> np.setdiff1d(a, b)\n    array([1, 2])\n\n    \"\"\"\n    if assume_unique:\n        ar1 = np.asarray(ar1).ravel()\n    else:\n        ar1 = unique(ar1)\n        ar2 = unique(ar2)\n    return ar1[_in1d(ar1, ar2, assume_unique=True, invert=True)]"
}
-/

/-- Find the set difference of two arrays.
    Return the unique values in `ar1` that are not in `ar2`. -/
def setdiff1d {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) : Id (Vector Int k) :=
  sorry

/-- Specification: setdiff1d returns unique values from ar1 that are not in ar2.
    The result contains no duplicates and is sorted. -/
theorem setdiff1d_spec {n m k : Nat} (ar1 : Vector Int n) (ar2 : Vector Int m) :
    ⦃⌜True⌝⦄
    setdiff1d ar1 ar2
    ⦃⇓result => ⌜-- Each element in result is from ar1 and not in ar2
                 (∀ i : Fin k, ∃ j : Fin n, result.get i = ar1.get j ∧ 
                  ∀ l : Fin m, result.get i ≠ ar2.get l) ∧
                 -- No duplicates in result
                 (∀ i j : Fin k, i ≠ j → result.get i ≠ result.get j) ∧
                 -- Result is sorted
                 (∀ i j : Fin k, i < j → result.get i ≤ result.get j) ∧
                 -- All unique values from ar1 not in ar2 are included
                 (∀ val : Int, (∃ i : Fin n, ar1.get i = val ∧ ∀ j : Fin m, ar2.get j ≠ val) →
                  ∃ i : Fin k, result.get i = val)⌝⦄ := by
  sorry