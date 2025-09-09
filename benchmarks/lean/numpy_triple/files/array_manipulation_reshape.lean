/- 
{
  "name": "numpy.reshape",
  "category": "Shape Operations",
  "description": "Gives a new shape to an array without changing its data",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.reshape.html",
  "doc": "Gives a new shape to an array without changing its data.\n\nParameters\n----------\na : array_like\n    Array to be reshaped.\nshape : int or tuple of ints\n    The new shape should be compatible with the original shape. If\n    an integer, then the result will be a 1-D array of that length.\n    One shape dimension can be -1. In this case, the value is\n    inferred from the length of the array and remaining dimensions.\norder : {'C', 'F', 'A'}, optional\n    Read the elements of \`a\` using this index order, and place the\n    elements into the reshaped array using this index order.  'C'\n    means to read / write the elements using C-like index order,\n    with the last axis index changing fastest, back to the first\n    axis index changing slowest. 'F' means to read / write the\n    elements using Fortran-like index order, with the first index\n    changing fastest, and the last index changing slowest. Note that\n    the 'C' and 'F' options take no account of the memory layout of\n    the underlying array, and only refer to the order of indexing.\n    'A' means to read / write the elements in Fortran-like index\n    order if \`a\` is Fortran *contiguous* in memory, C-like order\n    otherwise.\nnewshape : int or tuple of ints, optional\n    Deprecated since version 2.1: Use shape instead.\ncopy : bool, optional\n    If True, then the array data is copied. If None (the default),\n    then the array may be copied or a view may be returned.\n\nReturns\n-------\nreshaped_array : ndarray\n    This will be a new view object if possible; otherwise, it will\n    be a copy.  Note there is no guarantee of the *memory layout* (C- or\n    Fortran- contiguous) of the returned array.\n\nExamples\n--------\n>>> a = np.array([[1,2,3], [4,5,6]])\n>>> np.reshape(a, 6)\narray([1, 2, 3, 4, 5, 6])\n>>> np.reshape(a, (3, -1))  # the unspecified value is inferred to be 2\narray([[1, 2],\n       [3, 4],\n       [5, 6]])",
  "signature": "numpy.reshape(a, /, shape=None, order='C', *, newshape=None, copy=None)",
  "source_location": "numpy/_core/fromnumeric.py"
}
-/

/-  Gives a new shape to an array without changing its data.

    This implementation focuses on the most common case: reshaping a 1D array
    to another 1D array with the same total number of elements. The elements
    are preserved in the same linear order (C-order).

    For simplicity, this specification handles only 1D to 1D reshaping where
    the sizes are explicitly equal. More complex reshaping operations (like
    multidimensional arrays or -1 inference) would require additional machinery.
-/

/-  Specification: reshape preserves all elements in their linear order.

    The reshape operation creates a new vector with a different size parameter
    but maintains the same elements in the same order. This is the fundamental
    property of reshape - it's purely a "view" operation that doesn't modify data.

    Mathematical properties:
    1. Size preservation: The total number of elements remains constant
    2. Order preservation: Elements appear in the same linear sequence
    3. Value preservation: Each element value is unchanged

    Precondition: The new shape must have the same total size as the original
    Postcondition: Each element at index i in the result equals the element
                   at the corresponding index in the original array
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def reshape {n m : Nat} (a : Vector Float n) (h_size : n = m) : Id (Vector Float m) :=
  sorry

theorem reshape_spec {n m : Nat} (a : Vector Float n) (h_size : n = m) :
    ⦃⌜n = m⌝⦄
    reshape a h_size
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = a.get (i.cast h_size.symm)⌝⦄ := by
  sorry
