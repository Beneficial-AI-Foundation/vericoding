/* Roll array elements along a given axis by cyclically shifting elements.
Elements that roll beyond the last position are re-introduced at the first.

Specification: roll cyclically shifts array elements by the given amount.
For positive shift, elements move to the right and wrap around.
For negative shift, elements move to the left and wrap around.
Empty vectors are returned unchanged.

Mathematical property: result[i] = a[(i - shift) mod n]
where the modulo operation handles negative values correctly. */

use vstd::prelude::*;

verus! {
spec fn euclidean_mod(a: int, n: int) -> int
    requires n > 0
{
    ((a % n) + n) % n
}
fn roll<T: Copy>(a: Vec<T>, shift: i64) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        a.len() == 0 ==> result@ == a@,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = euclidean_mod(i - shift, a.len() as int);
            result[i] == a[src_idx]
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}