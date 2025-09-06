/* 
{
  "name": "numpy.nanargmax",
  "category": "Index finding",
  "description": "Return the indices of the maximum values in the specified axis ignoring NaNs",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.nanargmax.html",
  "doc": "Return the indices of the maximum values in the specified axis ignoring NaNs.\n\nFor all-NaN slices ``ValueError`` is raised. Warning: the results cannot be trusted if a slice contains only NaNs and -Infs.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : int, optional\n    Axis along which to operate. By default flattened input is used.\nout : array, optional\n    If provided, the result will be inserted into this array.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nindex_array : ndarray\n    An array of indices or a single index value.",
}
*/

/*  Returns the index of the maximum value in a non-empty vector, ignoring NaN values.
    
    This function finds the index of the maximum value among all non-NaN elements in the vector.
    Requires that at least one element is not NaN, otherwise it would raise an error.
    
    In case of multiple occurrences of the maximum values, the indices
    corresponding to the first occurrence are returned.
*/

/*  Specification: nanargmax returns the index of the first maximum element among non-NaN values.
    
    This comprehensive specification captures:
    1. The returned index points to an element that is not NaN
    2. The element at the returned index is the maximum among all non-NaN elements
    3. The function returns the first occurrence of the maximum value (among non-NaN elements)
    4. The returned index is valid (type-safe with bounds checking)
    5. The precondition ensures at least one element is not NaN
    6. All non-NaN elements are less than or equal to the maximum
    7. Among elements with the same maximum value, the first index is returned
*/
use vstd::prelude::*;

verus! {
// <vc-helpers>
spec fn is_nan(f: f32) -> bool {
    arbitrary()
}

spec fn float_le(x: f32, y: f32) -> bool {
    arbitrary()
}
// </vc-helpers>
fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !is_nan(a[i])
    ensures 
        result < a.len(),
        !is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !is_nan(a[j]) ==> float_le(a[j], a[result as int]),
        forall|j: int| 0 <= j < a.len() && !is_nan(a[j]) && a[j] == a[result as int] ==> result <= j
// <vc-implementation>
{
    assume(false);
    return 0; // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn nanargmax_spec(a: Vec<f32>)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !is_nan(a[i])
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>

fn main() {}

}