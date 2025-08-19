import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.size",
  "category": "Basic Operations",
  "description": "Return the number of elements along a given axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.size.html",
  "doc": "Return the number of elements along a given axis.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : int, optional\n    Axis along which the elements are counted. By default, give\n    the total number of elements.\n\nReturns\n-------\nelement_count : int\n    Number of elements along the specified axis.\n\nExamples\n--------\n>>> a = np.array([[1,2,3],[4,5,6]])\n>>> np.size(a)\n6\n>>> np.size(a,1)\n3\n>>> np.size(a,0)\n2",
  "code": "@array_function_dispatch(_size_dispatcher)\ndef size(a, axis=None):\n    \"\"\"\n    Return the number of elements along a given axis.\n    \"\"\"\n    if axis is None:\n        try:\n            return a.size\n        except AttributeError:\n            return asarray(a).size\n    else:\n        try:\n            return a.shape[axis]\n        except AttributeError:\n            return asarray(a).shape[axis]",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.size(a, axis=None)"
}
-/

open Std.Do

/-- Returns the number of elements in a vector -/
def size {n : Nat} (a : Vector Float n) : Id Nat :=
  sorry

/-- Specification: size returns the length of the vector, which is its type parameter n -/
theorem size_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    size a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  sorry