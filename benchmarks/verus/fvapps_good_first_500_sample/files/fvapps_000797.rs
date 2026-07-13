// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn array_xor(arr: Seq<u32>) -> u32 
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else if arr.len() == 1 {
        arr[0]
    } else {
        arr[0] ^ array_xor(arr.skip(1))
    }
}

fn solve_array_xor(n: usize, arr: Vec<u32>) -> (result: u32)
    requires 
        n == arr.len(),
        n > 0
    ensures
        result == array_xor(arr@)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // #guard_msgs in
    // #eval solve_array_xor 5 [8, 4, 1, 5, 0]

    // #guard_msgs in
    // #eval solve_array_xor 5 [1, 2, 4, 0, 8]

    // #guard_msgs in
    // #eval solve_array_xor 2 [10, 10]
}