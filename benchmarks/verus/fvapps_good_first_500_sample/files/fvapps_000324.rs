// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_jumps(arr: Vec<i32>) -> (result: i32)
    requires arr.len() > 0,
    ensures 
        result >= -1,
        result <= arr.len() as i32
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

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // min_jumps([100, -23, -23, 404, 100, 23, 23, 23, 3, 404]) == 3
    // min_jumps([7]) == 0
    // min_jumps([7, 6, 9, 6, 9, 6, 9, 7]) == 1
}