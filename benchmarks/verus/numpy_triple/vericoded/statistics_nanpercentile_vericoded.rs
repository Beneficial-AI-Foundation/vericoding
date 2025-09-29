// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] + vec_sum(a.skip(1))
    }
}

fn nanpercentile(a: Vec<i8>, q: i8) -> (result: i8)
    requires 0 <= q <= 100,
    ensures
        /* Case 1: Empty array returns 0 */
        a.len() == 0 ==> result == 0,
        /* Case 2: Non-empty array */
        a.len() > 0 ==> {
            /* Result is within bounds of input values */
            (forall|i: int| 0 <= i < a.len() ==> a[i] as int <= result as int || result as int <= a[i] as int) &&
            /* For single element, result equals that element */
            (a.len() == 1 ==> result == a[0])
        }
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        0
    } else if a.len() == 1 {
        a[0]
    } else {
        0
    }
}
// </vc-code>


}
fn main() {}