/* numpy.allclose: Returns True if two arrays are element-wise equal within a tolerance.

The tolerance values are positive, typically very small numbers. The
relative difference (rtol * abs(b)) and the absolute difference
atol are added together to compare against the absolute difference
between a and b.

For each element, the condition is:
absolute(a - b) <= (atol + rtol * absolute(b))

This function returns True if ALL elements satisfy this condition,
False otherwise.

Specification: allclose returns true iff all elements are within tolerance.

Precondition: rtol >= 0 and atol >= 0 (tolerance values must be non-negative)
Postcondition: result = true iff all elements satisfy the tolerance condition
               abs(a[i] - b[i]) <= atol + rtol * abs(b[i]) for all i */

use vstd::prelude::*;

verus! {
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
fn allclose(a: &Vec<i32>, b: &Vec<i32>, rtol: i32, atol: i32) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> 
            int_abs(a[i] as int - b[i] as int) <= (atol as int) + (rtol as int) * int_abs(b[i] as int)),
{
    // impl-start
    assume(false);
    false
    // impl-end
}
}
fn main() {}