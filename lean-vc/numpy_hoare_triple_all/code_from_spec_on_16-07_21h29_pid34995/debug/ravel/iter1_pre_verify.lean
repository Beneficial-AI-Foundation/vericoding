import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.ravel",
  "category": "Shape Operations",
  "description": "Return a contiguous flattened array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ravel.html",
  "doc": "Return a contiguous flattened array.\n\nA 1-D array, containing the elements of the input, is returned. A copy is\nmade only if needed.\n\nParameters\n----------\na : array_like\n    Input array. The elements in \`a\` are read in the order specified by\n    \`order\`, and packed as a 1-D array.\norder : {'C','F', 'A', 'K'}, optional\n    The elements of \`a\` are read using this index order. 'C' means\n    to index the elements in row-major, C-style order,\n    with the last axis index changing fastest, back to the first\n    axis index changing slowest. 'F' means to index the elements\n    in column-major, Fortran-style order, with the\n    first index changing fastest, and the last index changing\n    slowest. Note that the 'C' and 'F' options take no account of\n    the memory layout of the underlying array, and only refer to\n    the order of axis indexing. 'A' means to read the elements in\n    Fortran-like index order if \`a\` is Fortran *contiguous* in\n    memory, C-like order otherwise. 'K' means to read the\n    elements in the order they occur in memory, except for\n    reversing the data when strides are negative. By default, 'C'\n    index order is used.\n\nReturns\n-------\ny : array_like\n    y is a contiguous 1-D array with the same type as the input.\n\nExamples\n--------\n>>> x = np.array([[1, 2, 3], [4, 5, 6]])\n>>> np.ravel(x)\narray([1, 2, 3, 4, 5, 6])",
  "code": "@array_function_dispatch(_ravel_dispatcher)\ndef ravel(a, order='C'):\n    \"\"\"Return a contiguous flattened array.\"\"\"\n    if isinstance(a, np.matrix):\n        return asarray(a).ravel(order=order)\n    else:\n        return asanyarray(a).ravel(order=order)",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.ravel(a, order='C')"
}
-/

/-- numpy.ravel: Return a contiguous flattened array.

    For 1D arrays, ravel returns the input array unchanged since it's already
    flat. This reflects numpy's behavior where raveling a 1D array has no effect.
    
    For multi-dimensional arrays (not covered here), ravel would flatten them
    into a 1D array following the specified order ('C' for row-major, 'F' for
    column-major, etc.).
-/
def ravel {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  return a

/-- Specification: numpy.ravel returns the input vector unchanged for 1D arrays.

    Precondition: True (no special preconditions for 1D ravel)
    Postcondition: The result is identical to the input vector, maintaining
                   all elements in their original order
-/
theorem ravel_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    ravel a
    ⦃⇓result => ⌜result = a⌝⦄ := by
  unfold ravel
  simp [bind_pure_comp]
  constructor
  trivial
  simp