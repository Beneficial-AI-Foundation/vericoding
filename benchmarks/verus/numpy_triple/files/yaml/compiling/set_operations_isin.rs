/* numpy.isin: Element-wise test for membership in another array.

Calculates `element in test_elements`, broadcasting over `element` only.
Returns a boolean array of the same shape as `element` that is True
where an element of `element` is in `test_elements` and False otherwise.

This is an element-wise function version of the python keyword `in`.
For 1-D arrays, this is roughly equivalent to:
`np.array([item in test_elements for item in element])`

Specification: numpy.isin returns a boolean vector where each element indicates
whether the corresponding element in the input vector is found in test_elements.

Precondition: True (no special preconditions needed)
Postcondition: For all indices i, result[i] = true iff element[i] is in test_elements */

use vstd::prelude::*;

verus! {
fn numpy_isin(element: Vec<f32>, test_elements: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == element.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[i] == test_elements[j])
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}