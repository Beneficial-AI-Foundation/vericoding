// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_longest_segment(n: usize, k: u32, nums: Vec<u32>) -> (result: usize)
    requires 
        n > 0,
        nums.len() == n,
    ensures
        result <= n,
        result >= 0,
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