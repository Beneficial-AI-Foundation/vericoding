/* numpy.strings.lstrip: For each element in a vector, return a copy with the leading characters removed.

Removes leading characters from each string element in the input vector. The behavior
depends on the chars parameter:
- If chars is None, whitespace characters are removed from the beginning
- If chars is provided, any combination of those characters is removed from the beginning

The function preserves the shape of the input array and handles empty strings
appropriately by returning them unchanged.

From NumPy documentation:
- Parameters: a (array_like) - Input array with string dtype
              chars (optional) - Characters to remove from the beginning
- Returns: out (ndarray) - Output array with leading characters removed

Mathematical Properties:
1. Element-wise transformation: result[i] = lstrip(a[i], chars) for all i
2. Length preservation or reduction: result[i].length ≤ a[i].length for all i
3. Prefix removal: result[i] is a suffix of a[i] for all i
4. Character set removal: only characters in chars are removed from the beginning
5. Preserves vector length: result.size = a.size */

use vstd::prelude::*;

verus! {
fn lstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            let original = #[trigger] a[i];
            let result_str = #[trigger] result[i];
            /* Length preservation or reduction */
            result_str@.len() <= original@.len() &&
            /* Suffix property: result is a suffix of original */
            (exists|k: int| 0 <= k <= original@.len() && 
             result_str@ == original@.subrange(k, original@.len() as int)) &&
            /* Empty string case: if original is empty, result is empty */
            (original@.len() == 0 ==> result_str@.len() == 0)
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}