/* numpy.strings.lower: Return an array with the elements converted to lowercase.

Converts each string element in the input vector to lowercase. This transformation
applies to all alphabetic characters while preserving non-alphabetic characters
(digits, punctuation, whitespace) unchanged.

The function preserves the shape of the input array and handles empty strings
appropriately by returning them unchanged.

From NumPy documentation:
- Parameters: a (array_like) - Input array with string dtype
- Returns: out (ndarray) - Output array with elements converted to lowercase

Mathematical Properties:
1. Element-wise transformation: result[i] = lower(a[i]) for all i
2. Length preservation: result[i].length = a[i].length for all i
3. Case transformation: uppercase letters become lowercase, others unchanged
4. Idempotent: lower(lower(x)) = lower(x)
5. Preserves vector length: result.size = a.size */

use vstd::prelude::*;

verus! {
fn lower(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let original = a[i];
            let res_str = result[i];
            /* Fundamental correctness: result matches lowercase conversion */
            &&& (res_str.len() == original.len())
            /* Empty string case: empty input produces empty output */
            &&& (original.len() == 0 ==> res_str == "")
            /* Length preservation */
            &&& (res_str.len() == original.len())
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}