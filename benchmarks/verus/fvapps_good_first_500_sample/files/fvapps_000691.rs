// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maxval(arr: Vec<i32>) -> (result: i32)
    requires arr.len() >= 4,
    ensures 
        exists|a: int, b: int, c: int, d: int| 
            0 <= a < b && b < c && c < d && d < arr.len() &&
            result == arr[d] - arr[c] + arr[b] - arr[a],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}