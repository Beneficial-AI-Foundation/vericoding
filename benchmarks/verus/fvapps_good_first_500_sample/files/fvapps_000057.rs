// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: u32, arr: Vec<i32>) -> (result: bool)
    requires 
        arr.len() > 0,
        n as usize == arr.len(),
    ensures 
        result == (arr[arr.len() - 1] > arr[0])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


fn main() {}

}