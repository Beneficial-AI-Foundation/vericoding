/* Return an array with the elements converted to lowercase.

numpy.strings.lower: Return an array with the elements converted to lowercase.

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
5. Preserves vector length: result.size = a.size

Specification: numpy.strings.lower returns a vector where each string element
is converted to lowercase.

Mathematical Properties:
1. Element-wise correctness: Each element is correctly converted to lowercase
2. Length preservation: Each transformed string has the same length as the original
3. Case transformation: Uppercase letters become lowercase, others unchanged
4. Idempotent property: Applying lower twice gives the same result as applying it once
5. Empty string handling: Empty strings remain empty
6. Character-level correctness: Each character is correctly transformed

Precondition: True (no special preconditions for lowercase conversion)
Postcondition: For all indices i, result[i] is the lowercase version of a[i] */

use vstd::prelude::*;

verus! {
fn lower(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == #[trigger] a[i]@.len(),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == 0),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}