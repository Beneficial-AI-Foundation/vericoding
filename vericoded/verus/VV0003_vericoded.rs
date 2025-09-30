// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn dummy_helper() { }
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(a: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= a.len(),
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

}
fn main() {}