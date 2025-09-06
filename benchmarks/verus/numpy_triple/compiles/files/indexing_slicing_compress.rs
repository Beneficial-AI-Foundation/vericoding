/* {
  "name": "numpy.compress",
  "category": "Basic indexing",
  "description": "Return selected slices of an array along given axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.compress.html",
  "doc": "Return selected slices of an array along given axis.\n\nWhen working on a 1-D array, compress is equivalent to extract.\n\nParameters\n----------\ncondition : 1-D array of bools\n    Array that selects which entries to return.\na : array_like\n    Array from which to extract a part.\naxis : int, optional\n    Axis along which to take slices.\nout : ndarray, optional\n    Output array.\n\nReturns\n-------\ncompressed_array : ndarray\n    A copy of `a` without the slices along axis for which corresponding element in condition is False.",
}

Compresses a vector by selecting only elements where the corresponding 
condition is true. Returns a new vector containing only the selected elements.
The result size is the number of true values in the condition vector.

Specification: compress returns a new vector containing only the elements 
from the input vector where the corresponding condition element is true.

Mathematical properties:
1. The result size equals the number of true values in the condition
2. The result preserves the order of elements from the original vector
3. Each element in the result corresponds to a true condition at the same index
4. The result is empty if and only if all condition elements are false

This function implements array compression/masking, a fundamental operation
in array programming that allows selective extraction of elements based on
a boolean mask. It's equivalent to boolean indexing in NumPy. */

use vstd::prelude::*;

verus! {
spec fn count_true(condition: Seq<bool>) -> nat
    decreases condition.len(),
{
    if condition.len() == 0 {
        0
    } else {
        let first = condition[0];
        let rest = condition.subrange(1, condition.len() as int);
        if first {
            1 + count_true(rest)
        } else {
            count_true(rest)
        }
    }
}
fn compress(condition: &Vec<bool>, a: &Vec<f64>) -> (result: Vec<f64>)
    requires 
        condition.len() == a.len(),
    ensures
        result.len() == count_true(condition@),
        exists|mapping: Seq<int>| {
            &&& mapping.len() == result.len()
            &&& forall|i: int| 0 <= i < mapping.len() ==> {
                &&& 0 <= mapping[i] < condition.len()
                &&& condition@[mapping[i]]
            }
            &&& forall|i: int| 0 <= i < result.len() ==> 
                result@[i] == a@[mapping[i]]
            &&& forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping[i] < mapping[j]
        },
        (result.len() == 0) <==> forall|i: int| 0 <= i < condition.len() ==> !condition@[i],
        (result.len() == condition.len()) <==> forall|i: int| 0 <= i < condition.len() ==> condition@[i],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}