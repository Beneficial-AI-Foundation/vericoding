/*
{
  "name": "numpy.any",
  "category": "Truth value testing",
  "description": "Test whether any array element along a given axis evaluates to True",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.any.html",
  "doc": "Test whether any array element along a given axis evaluates to True.\n\nReturns single boolean if axis is None\n\nParameters\n----------\na : array_like\n    Input array or object that can be converted to an array.\naxis : None or int or tuple of ints, optional\n    Axis or axes along which a logical OR reduction is performed.\n    The default (axis=None) is to perform a logical OR over all\n    the dimensions of the input array. axis may be negative, in\n    which case it counts from the last to the first axis.\n    \n    .. versionadded:: 1.7.0\n    \n    If this is a tuple of ints, a reduction is performed on multiple\n    axes, instead of a single axis or all the axes as before.\nout : ndarray, optional\n    Alternate output array in which to place the result. It must have\n    the same shape as the expected output and its type is preserved\n    (e.g., if it is of type float, then it will remain so, returning\n    1.0 for True and 0.0 for False, regardless of the type of a).\n    See Output type determination for more details.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left\n    in the result as dimensions with size one. With this option,\n    the result will broadcast correctly against the input array.\n    \n    If the default value is passed, then keepdims will not be\n    passed through to the any method of sub-classes of\n    ndarray, however any non-default value will be. If the\n    sub-class' method does not implement keepdims any\n    exceptions will be raised.\nwhere : array_like of bool, optional\n    Elements to include in checking for any True values.\n    See reduce for details.\n    \n    .. versionadded:: 1.20.0\n\nReturns\n-------\nany : bool or ndarray\n    A new boolean or ndarray is returned unless out is specified,\n    in which case a reference to out is returned.\n\nSee Also\n--------\nndarray.any : equivalent method\n\nall : Test whether all elements along a given axis evaluate to True.\n\nNotes\n-----\nNot a Number (NaN), positive infinity and negative infinity evaluate\nto True because these are not equal to zero.\n\nExamples\n--------\n>>> np.any([[True, False], [True, True]])\nTrue\n\n>>> np.any([[True, False], [False, False]], axis=0)\narray([ True, False])\n\n>>> np.any([-1, 0, 5])\nTrue\n\n>>> np.any(np.nan)\nTrue\n\n>>> np.any([[True, False], [False, False]], where=[[False], [True]])\nFalse\n\n>>> o=np.array(False)\n>>> z=np.any([-1, 4, 5], out=o)\n>>> z, o\n(array(True), array(True))\n>>> # Check now that z is a reference to o\n>>> z is o\nTrue\n>>> id(z), id(o) # identity of z and o              # doctest: +SKIP\n(191614240, 191614240)",
}
*/

/*  Test whether any element in a vector evaluates to True.
    
    For numeric types, returns true if any element is non-zero.
    Special values like NaN, positive/negative infinity are considered True.
    This follows NumPy's convention where non-zero values are truthy.
    
    This is a reduction operation that performs logical OR across all elements,
    treating non-zero values as True and zero as False. */

/*  Specification: `any` returns true if and only if at least one element in the vector is non-zero.
    
    The specification captures comprehensive mathematical properties:
    1. Logical equivalence: result is true iff there exists a non-zero element
    2. Completeness: result is false iff all elements are zero
    3. Empty vector behavior: returns false for empty vectors
    4. Monotonicity: adding more elements can only increase the chance of being true
    
    This matches NumPy's behavior where:
    - Non-zero values (including NaN, ±∞) evaluate to True
    - Only zero evaluates to False
    - Empty arrays return False */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
spec fn any(v: Vec<f64>) -> bool;
// <vc-implementation>
// TODO: Remove this line and implement the function body
// </vc-implementation>
proof fn any_theorem(v: Vec<f64>)
    ensures
        /* Core logical equivalence */
        any(v) == true <==> exists|i: int| 0 <= i < v.len() && v[i] != 0.0,
        any(v) == false <==> forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0,
        /* Boundary conditions */
        v.len() == 0 ==> any(v) == false,
        /* Monotonicity properties */
        (forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0) ==> any(v) == false,
        (exists|i: int| 0 <= i < v.len() && v[i] != 0.0) ==> any(v) == true,
        /* Logical consistency */
        any(v) == true || any(v) == false,
        !(any(v) == true && any(v) == false)
{
// <vc-proof>
    assume(false); // TODO: Remove this line and implement the proof
// </vc-proof>
}

fn main() {
}

}