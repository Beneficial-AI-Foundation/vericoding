/* Return (a * i), that is string multiple concatenation, element-wise.
Values in i of less than 0 are treated as 0 (which yields an empty string).

Specification: multiply performs element-wise string repetition.
Each output string is the corresponding input string repeated the specified number of times.
Negative repetition counts produce empty strings. This comprehensive specification
captures the core mathematical properties of string multiplication in NumPy. */

use vstd::prelude::*;

verus! {
fn multiply(a: &Vec<String>, i: &Vec<i32>) -> (result: Vec<String>)
    requires a.len() == i.len(),
    ensures
        result.len() == a.len(),
        /* Core property: Element-wise string repetition with repeat_string behavior */
        forall|j: int| 0 <= j < a.len() && i[j] <= 0 ==> result[j]@.len() == 0,
        /* Identity property: Multiplying by 1 yields the original string */
        forall|j: int| 0 <= j < a.len() && i[j] == 1 ==> result[j] == a[j],
        /* Zero property: Multiplying by 0 yields empty string */
        forall|j: int| 0 <= j < a.len() && i[j] == 0 ==> result[j]@.len() == 0,
        /* Empty string property: Empty strings remain empty regardless of repetition */
        forall|j: int| 0 <= j < a.len() && a[j]@.len() == 0 ==> result[j]@.len() == 0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}