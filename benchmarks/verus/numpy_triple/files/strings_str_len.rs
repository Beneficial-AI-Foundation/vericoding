/* Returns the length of each string element in the vector.
For Unicode strings, this counts the number of Unicode code points.

Specification: str_len returns the length (number of Unicode code points) of each string element.

Preconditions: None (str_len is defined for all strings)

Postconditions:
- The result vector has the same size as the input vector
- Each element in the result corresponds to the length of the corresponding input string
- Length is always non-negative (natural number)
- Empty strings have length 0
- Length is measured in Unicode code points for Unicode strings */

use vstd::prelude::*;

verus! {
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}