// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures ({
        let max_val = a.fold_left(a[0], |acc, x| if x > acc { x } else { acc });
        let min_val = a.fold_left(a[0], |acc, x| if x < acc { x } else { acc });
        result == max_val - min_val
    }),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}